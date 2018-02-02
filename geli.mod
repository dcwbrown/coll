MODULE geli;  (* GELI - Generated lists *)

IMPORT TextWriter, SYSTEM;

TYPE

  Atom = POINTER TO AtomDesc; AtomDesc = RECORD END;
  List = POINTER TO ListDesc; ListDesc = RECORD (AtomDesc) next: List     END;
  Ch   = POINTER TO ChDesc;   ChDesc   = RECORD (ListDesc) ch:   LONGINT  END;
  Int  = POINTER TO IntDesc;  IntDesc  = RECORD (ListDesc) int:  LONGINT  END;
  Link = POINTER TO LinkDesc; LinkDesc = RECORD (ListDesc) link: Atom     END;

  Function = PROCEDURE(): List;
  Fn = POINTER TO FnDesc; FnDesc = RECORD (ListDesc) fn: Function END;

VAR
   Abort: BOOLEAN;
   Stack: List;

PROCEDURE (a: Atom) Next(): Atom; BEGIN RETURN NIL    END Next;
PROCEDURE (a: List) Next(): Atom; BEGIN RETURN a.next END Next;


(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE nzlen(s: ARRAY OF CHAR): LONGINT;
VAR result: LONGINT;
BEGIN result := 0;
  WHILE (result < LEN(s)) & (s[result] # 0x) DO INC(result) END;
RETURN result END nzlen;

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


(* -------------------------------- Utility --------------------------------- *)

PROCEDURE WriteAtom(a: Atom);
BEGIN
  WITH
    a: Ch   DO wc(CHR(a.ch))
  | a: Int  DO wi(a.int)
  | a: Link DO ws("<LINK>") (*ws(".[."); WriteList(a.link); ws(".].")*)
  | a: Fn   DO ws("<FUNCTION>")
  ELSE         ws("<UNRECOGNISED>")
  END
END WriteAtom;

PROCEDURE WriteList(l: Atom);
BEGIN
  IF l = NIL THEN wsl("<empty list>")
  ELSE
    WHILE (l # NIL) DO
      IF l IS Link THEN WriteList(l(Link).link) ELSE WriteAtom(l) END;
      l := l.Next()
    END
  END
END WriteList;

PROCEDURE WriteStack(l: List);
BEGIN
  IF l = NIL THEN wsl("<empty stack>")
  ELSE
    IF l.next # NIL THEN WriteStack(l.next) END;
    ws("<");
    IF l IS Link THEN WriteList(l(Link).link) ELSE WriteAtom(l) END;
    ws(">")
  END
END WriteStack;

PROCEDURE MakeLink(l: List): Link;
VAR result: Link;
BEGIN NEW(result); result.link := l;
RETURN result END MakeLink;

(*
PROCEDURE AtomAsInt(a: Atom): LONGINT;
BEGIN
RETURN a(Int).int END AtomAsInt;
*)

PROCEDURE Append(l1, l2: List);
BEGIN
  Assert(l1 # NIL, "Cannot append to nonexistent (empty) list.");
  WHILE l1.next # NIL DO l1 := l1.next END;
  l1.next := l2
END Append;

PROCEDURE MakeText(s: ARRAY OF CHAR): List;
VAR result: List; i: LONGINT; ch: Ch;
BEGIN result := NIL;
  i := LEN(s)-1;
  WHILE (i >= 0) & (s[i] = 0X) DO DEC(i) END; (* Discard trailing 0 characters *)
  WHILE i >= 0 DO
    NEW(ch); ch.ch := ORD(s[i]); ch.next := result;
    result := ch; DEC(i)
  END;
RETURN result END MakeText;

PROCEDURE Push(VAR l: List; a: Atom);
BEGIN
  (*Assert(a IS List, "Push expects atom being pushed to be a list");*)
  a(List).next := l;
  l := a(List)
END Push;

PROCEDURE Evaluate(a: Atom);
VAR n: Atom; l: List;
BEGIN
  WHILE a # NIL DO
    n := a.Next();
    IF a IS Fn THEN
      l := a(Fn).fn();  (* Execute intrinsic function *)
      IF l # NIL THEN Push(Stack, MakeLink(l)) END
    ELSE
      Push(Stack, a)
    END;
    a := n
  END
END Evaluate;

PROCEDURE FnTest(): List;
BEGIN wlc; wsl("** Intrinsic test evaluated **");
RETURN NIL END FnTest;

PROCEDURE MakeFn(fn: Function): List;
VAR result: Fn;
BEGIN NEW(result); result.fn := fn;
RETURN result END MakeFn;

** Implement iota generator function


PROCEDURE Test();
VAR a: Atom; l: List;
BEGIN
  a := MakeText("Hello.");  WriteList(a); wl;

  l := MakeText("alpha ");
  Append(l, MakeLink(MakeText("nested")));
  Append(l, MakeText(" beta."));
  WriteList(l); wl;

  Evaluate(MakeFn(FnTest));

  Evaluate(l);
  WriteStack(Stack); wl;

END Test;


BEGIN Abort := FALSE;
  Test
END geli.
