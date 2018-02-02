MODULE brace;  (* brace - forthish lispish language with just nesting in the core *)

(*

    Basic text representation is one atom per node.

    Over time, static strings of atoms are re-represented as byte arrays.

    Atoms are 64 bit values that can be
      -  a character code (Unicode 21 bit value)
      -  a numeric value (integer or floating point)
      -  a memory reference to an atom or string

    The interpretation of the 64 bits is entirely dependent on context. There
    are no flags in the atom itself to determine context.

    All atoms and strings include both the value and a forward pointer.

    The string byte encoding is encoded so as to compress character values and
    small integers.

    0xxxxxxx          - 7 bit small integer/character
    10000000          - Reserved marker flag
    10xxxxxx cyyyyyyy - Positive integer value or character of 6+7n bits
                        xxxxxx are the most significant bits (after the implicit sign of 0)
                        xxxxxx must be non zero.
                        c is the continuation flag, the last byte has c=0
    110xxxxx          - 5 bit small negative integer
    111xxxxx cyyyyyyy - Negative integer value of 5+7n bits
                        xxxxx are the most significant bits (after the implicit sign of 1)
                        c is the continuation flag, the last byte has c=0
 *)

IMPORT TextWriter, SYSTEM;

CONST
  (* Dispenser actions *)
  ThisNode    = 0;
  AdvanceNode = 1;
  Rewind      = 2;

TYPE
  Node = POINTER TO NodeDesc; NodeDesc = RECORD next: Node END;
  Data = POINTER TO DataDesc; DataDesc = RECORD (NodeDesc) data: LONGINT END;
  Link = POINTER TO LinkDesc; LinkDesc = RECORD (NodeDesc) link: Node    END;

  Function = PROCEDURE(): Node;

  DispenserState = RECORD END;
  DispenserAction: SHORTINT;
  Dispenser = RECORD
    handler: PROCEDURE(VAR state: DispenserState; action: DispenserAction): Node
  END;

  ListDispenserState = RECORD(DispenserState) first, current: Node END;
  IotaDispenserState = RECORD(DispenserState) current: LONGINT END;

VAR
   Abort: BOOLEAN;
   Stack: Node;
   P:     Node;  (* Program pointer (next instruction) *)
   I:     Node;  (* Current instruction *)

(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)  END ws;
PROCEDURE wc(c: CHAR);           BEGIN TextWriter.Char(c)    END wc;
PROCEDURE wl;                    BEGIN TextWriter.NewLine    END wl;
PROCEDURE wi(i: LONGINT);        BEGIN TextWriter.Integer(i) END wi;
PROCEDURE wnb;                   BEGIN TextWriter.NoBreak    END wnb;
PROCEDURE wlc;                   BEGIN TextWriter.StartLine  END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl             END wsl;


(* ----------------- Error handling convenience functions ------------------- *)

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Internal error:"); wsl(msg); HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* ------------------------------- Dispensers ------------------------------- *)

PROCEDURE Advance(VAR d: Dispenser);
BEGIN WITH
    d: ListDispenser DO IF d.current # NIL THEN d.current := d.current.next END
  | d: IotaDispenser DO INC(d.current)
  ELSE Fail("Advance called on abstract dispenser.")
  END
END Advance;

PROCEDURE IsLink(VAR d: Dispenser): BOOLEAN;
VAR result: BOOLEAN;
BEGIN result := FALSE;
  WITH d: ListDispenser DO result := (d.current # NIL) & (d.current IS Link) END
RETURN result END IsLink;

PROCEDURE GetLink(VAR d: Dispenser): Node;
VAR result: Node;
BEGIN result := NIL;
  WITH d: ListDispenser DO
    IF d.current # NIL THEN
      WITH d.current.Link DO
        result := d.current.link.
      END
    END
  END
  ) & (d(ListDispenser).current # NIL) THEN
Fail("GetLink called on abstract dispenser.")
END GetLink;

PROCEDURE GetData(VAR d: Dispenser): LONGINT;
BEGIN
Fail("GetData called on abstract dispenser.")
END GetData;


PROCEDURE(VAR d: ListDispenser) Advance; BEGIN  END Advance;
PROCEDURE(VAR d: IotaDispenser) Advance; BEGIN INC(d.current) END Advance;



(* -------------------------------- Utility --------------------------------- *)

PROCEDURE WriteList(v: Node);
VAR l: Node;
BEGIN
  IF v = NIL THEN wsl("<empty list>")
  ELSE
    WHILE (v # NIL) DO
      IF v IS Link THEN ws(" ["); WriteList(v(Link).link); ws("] ")
      ELSE wi(v(Data).data)
      END;
      v := v.next
    END
  END
END WriteList;

PROCEDURE WriteStack(v: Node);
BEGIN
  IF v = NIL THEN wsl("<empty stack>")
  ELSE
    IF v.next # NIL THEN WriteStack(v.next) END;
    ws("<");
    WITH
      v: Link DO WriteList(v.link)
    | v: Data DO wi(v.data)
    END;
    ws(">")
  END
END WriteStack;

PROCEDURE MakeLink(v: Node): Link;
VAR result: Link;
BEGIN NEW(result); result.link := v;
RETURN result END MakeLink;

PROCEDURE Append(l1, l2: Node);
BEGIN
  Assert(l1 # NIL, "Cannot append to nonexistent (empty) list.");
  WHILE l1.next # NIL DO l1 := l1.next END;
  l1.next := l2
END Append;

PROCEDURE MakeText(s: ARRAY OF CHAR): Node;
VAR result: Node; i: LONGINT; ch: Data;
BEGIN result := NIL;
  i := LEN(s)-1;
  WHILE (i >= 0) & (s[i] = 0X) DO DEC(i) END; (* Discard trailing 0 characters *)
  WHILE i >= 0 DO
    NEW(ch); ch.data := ORD(s[i]); ch.next := result;
    result := ch; DEC(i)
  END;
RETURN result END MakeText;

PROCEDURE PushData(VAR s: Node; n: LONGINT);
VAR d: Data;
BEGIN NEW(d); d.data := n; d.next := s; s := d
END PushData;

PROCEDURE PushLink(VAR s: Node; n: Node);
VAR l: Node;
BEGIN NEW(l); l.link := n; l.next := s; s := l
END PushLink;

PROCEDURE Push(VAR l: Node; v: Node);
BEGIN WITH v: Link DO PushLink(v.link) | v: Data DO PushData(v.data) END
END Push;

PROCEDURE WriteInstruction(i: Node);
BEGIN
  wlc; ws("Instruction: ");
  IF i = NIL THEN       ws("<end>")
  ELSIF i IS Data THEN  wi(i(Data).data)
  ELSE                  WriteList(i(Link).link)
  END;
  wl
END WriteInstruction;

PROCEDURE intrinsic(i: LONGINT);
BEGIN
  CASE i OF
    0: wlc; wsl("** Intrinsic test evaluated **");
  | 1:
  ELSE wsl("Unrecognised intrinsic.");
  END
END intrinsic;

PROCEDURE Evaluate(l: Node);
VAR I: Node;
BEGIN
  P := l;  (* Set global program position *)
  WHILE P # NIL DO
    I := P;  P := P.next;
    WITH I: Link DO Push(Stack, I) | I: Data DO intrinsic(I.data) END;
  END
END Evaluate;



PROCEDURE Test();
VAR v: Node; l: Node;
BEGIN
  v := MakeText("Hello.");  WriteList(v); wl;

  l := MakeText("alpha ");
  Append(l, MakeLink(MakeText("nested")));
  Append(l, MakeText(" beta."));
  WriteList(l); wl;



  (*
  Evaluate(MakeFn(FnTest));

  Evaluate(l);
  WriteStack(Stack); wl;
  *)

END Test;


BEGIN Abort := FALSE;
  Test
END brace.
