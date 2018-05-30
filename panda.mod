MODULE panda;  (* panda - programs and nested data *)

IMPORT Strings, TextWriter, SYSTEM;

TYPE
  Atom   = POINTER TO AtomRec;  AtomRec = RECORD next: Atom END;
  Func   = PROCEDURE();

  Code = POINTER TO CodeRec;  CodeRec = RECORD (AtomRec) code: INTEGER END;
  Link = POINTER TO LinkRec;  LinkRec = RECORD (AtomRec) link: Atom END;
  (*Func = POINTER TO FuncRec;  FuncRec = RECORD (AtomRec) func: Func END;*)

AddState = RECORD
  first: Atom;
  curr:  Atom;
  stack: Link;
  esc:   BOOLEAN;
END;


VAR
  Abort: BOOLEAN;


(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)              END ws;
PROCEDURE wc(c: CHAR);           BEGIN TextWriter.Char(c)                END wc;
PROCEDURE wl;                    BEGIN TextWriter.NewLine                END wl;
PROCEDURE wi(i: LONGINT);        BEGIN TextWriter.Integer(i)             END wi;
PROCEDURE wx(i,n: LONGINT);      BEGIN TextWriter.Hex(i,n)               END wx;
PROCEDURE wnb;                   BEGIN TextWriter.NoBreak                END wnb;
PROCEDURE wlc;                   BEGIN TextWriter.StartLine              END wlc;
PROCEDURE wfl;                   BEGIN TextWriter.Flush                  END wfl;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl                         END wsl;
PROCEDURE space(i: LONGINT);     BEGIN WHILE i>0 DO ws("  "); DEC(i) END END space;


(* ----------------- Error handling convenience functions ------------------- *)

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN IF Strings.Length(msg) > 0 THEN wlc; ws("Internal error:"); wsl(msg) END;
  wlc; HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* --------------------------------- Panda ---------------------------------- *)

PROCEDURE AddCharInternal(VAR state: AddState; ch: CHAR);
VAR code: Code;
BEGIN
  NEW(code);  code.code := ORD(ch);
  state.curr.next := code;
  state.curr := code;
END AddCharInternal;


PROCEDURE wt(a: Atom);
BEGIN
  ws("(wt) "); wfl;
  IF a = NIL THEN
    ws("NIL"); wfl;
  ELSE
    ws("non-NIL");
    wfl;
    IF    a IS Link THEN ws(": Link")
    ELSIF a IS Code THEN ws(": Code")
    ELSIF a IS Atom THEN ws(": Atom")
    ELSE ws(": unknown") END;
    wfl;
  END;
END wt;

PROCEDURE OpenNest(VAR state: AddState);
VAR link: Link;
BEGIN
  wsl("Enter OpenNest.");
  ws("Initial state.stack is "); wt(state.stack); wsl(".");
  NEW(link);
  wsl("OpenNest 1.");
  link.next := state.stack;
  wsl("OpenNest 2.");
  link.link := state.first;
  wsl("OpenNest 3.");
  state.stack := link;
  ws("OpenNest first push, state.stack.next is "); wt(state.stack.next); wsl(".");
  NEW(link); link.next := state.stack; link.link := state.curr;  state.stack := link;
  ws("OpenNest second push, state.stack.next is "); wt(state.stack.next); wsl(".");
  NEW(state.first); state.curr := state.first;
  wsl("Exit OpenNest.");
END OpenNest;

PROCEDURE CloseNest(VAR state: AddState);
VAR link: Link;
BEGIN
  wsl("Enter CloseNest.");
  NEW(link);
  link.link := state.first.next;
  wsl("CloseNest 1.");
  state.stack.link.next := link;
  wsl("CloseNest 2.");
  state.curr := link;
  wsl("CloseNest 3.");
  state.stack := state.stack.next(Link);
  wsl("CloseNest 4.");
  state.first := state.stack.link;
  wsl("CloseNest 5.");
  IF state.stack.next = NIL THEN
    wsl("CloseNest 6a.");
    state.stack := NIL
  ELSE
    wsl("CloseNest 6b.");
    ws("  state.stack.next IS "); wfl; wt(state.stack.next); wsl(".");
    state.stack := state.stack.next(Link)
  END;
  wsl("Exit CloseNest.");
END CloseNest;

PROCEDURE AddChar(VAR state: AddState; ch: CHAR);
BEGIN
  IF state.esc THEN
    AddCharInternal(state, ch);
    state.esc := FALSE
  ELSE
    IF    ch = '^' THEN state.esc := TRUE
    ELSIF ch = '[' THEN OpenNest(state)
    ELSIF ch = ']' THEN CloseNest(state)
    ELSE                AddCharInternal(state, ch)
    END
  END
END AddChar;

PROCEDURE AddText(s: ARRAY OF CHAR): Atom;
VAR state: AddState; i: INTEGER;
BEGIN
  NEW(state.first);
  state.curr  := state.first;
  state.stack := NIL;
  state.esc   := FALSE;
  i := 0;
  WHILE (i < LEN(s))  &  (s[i] # 0X) DO  AddChar(state, s[i]);  INC(i)  END;
RETURN state.first.next END AddText;

PROCEDURE DisplayText(a: Atom);
BEGIN
  WHILE a # NIL DO
    IF a IS Code THEN wc(CHR(a(Code).code)) END;
    a := a.next;
  END
END DisplayText;


(* -------------------------------- Startup --------------------------------- *)

BEGIN
  Abort:=FALSE;
  DisplayText(AddText("The ^^cat sat [on the] mat."));
  wlc
END panda.
