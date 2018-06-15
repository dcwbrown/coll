MODULE panda;  (* panda - programs and nested data *)

IMPORT Strings, Files, TextWriter, SYSTEM;

TYPE
  Atom   = POINTER TO AtomRec;  AtomRec = RECORD next: Atom END;
  Func   = PROCEDURE();

  Val = POINTER TO ValRec;  ValRec = RECORD (AtomRec) val: INTEGER END;
  Lnk = POINTER TO LnkRec;  LnkRec = RECORD (AtomRec) lnk: Atom END;
  (*Func = POINTER TO FuncRec;  FuncRec = RECORD (AtomRec) func: Func END;*)

  AddState = RECORD
    first: Atom;
    curr:  Atom;
    stack: Lnk;
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
VAR val: Val;
BEGIN
  NEW(val);  val.val := ORD(ch);
  state.curr.next := val;
  state.curr := val;
END AddCharInternal;


PROCEDURE wt(a: Atom);
BEGIN
  ws("(wt) "); wfl;
  IF a = NIL THEN
    ws("NIL"); wfl;
  ELSE
    ws("non-NIL");
    wfl;
    IF    a IS Lnk THEN ws(": Lnk")
    ELSIF a IS Val THEN ws(": Val")
    ELSIF a IS Atom THEN ws(": Atom")
    ELSE ws(": unknown") END;
    wfl;
  END;
END wt;

PROCEDURE OpenNest(VAR state: AddState);
VAR lnk: Lnk;
BEGIN
  NEW(lnk);
  lnk.next := state.stack;
  lnk.lnk := state.first;
  state.stack := lnk;
  NEW(lnk); lnk.next := state.stack; lnk.lnk := state.curr;  state.stack := lnk;
  NEW(state.first); state.curr := state.first;
END OpenNest;

PROCEDURE CloseNest(VAR state: AddState);
VAR lnk: Lnk;
BEGIN
  NEW(lnk);
  lnk.lnk := state.first.next;
  state.stack.lnk.next := lnk;
  state.curr := lnk;
  state.stack := state.stack.next(Lnk);
  state.first := state.stack.lnk;
  IF state.stack.next = NIL THEN
    state.stack := NIL
  ELSE
    state.stack := state.stack.next(Lnk)
  END;
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
    IF    a IS Val THEN wc(CHR(a(Val).val))
    ELSIF a IS Lnk THEN wc('['); DisplayText(a(Lnk).lnk); wc(']')
    END;
    a := a.next;
  END
END DisplayText;


(* ------------------------------ Core engine ------------------------------- *)

PROCEDURE FindString(VAR p, k: Atom): INTEGER;
VAR
  p2: Atom;
  ptest, ktest: Atom;  (* test alternative *)
  pbest, kbest: Atom;  (* best alternative *)
  count, ctest, cbest: INTEGER;
BEGIN count := 0;
  WHILE (p # NIL) & (k # NIL) DO
    Assert(k IS Val, "k must be Val in FindString");
    IF p IS Val THEN
      IF p(Val).val = k(Val).val THEN
        p := p.next;
        k := k.next;
        INC(count)
      ELSE
        RETURN count
      END
    ELSIF p IS Lnk THEN
      p2 := p(Lnk).lnk;
      pbest := NIL;  kbest := NIL;  cbest := 0;
      WHILE p2 # NIL DO
        Assert(p2 IS Lnk, "pattern must be Lnk in Alternate");
        ptest := p2(Lnk).lnk;
        ktest := k;
        ctest := FindString(ptest, ktest);
        IF ctest > cbest THEN pbest := ptest;  kbest := ktest;  cbest := ctest END;
        p2 := p2.next
      END;
      IF cbest > 0 THEN
        IF pbest = NIL THEN p := p.next ELSE p := pbest END;
        k := kbest;
        INC(count, cbest)
      ELSE
        RETURN count
      END
    ELSE
      Fail("p neither Val nor Lnk in FindString.")
    END
  END;
RETURN count END FindString;


(* -------------------------------- Startup --------------------------------- *)

PROCEDURE ReadInitialText(VAR s: ARRAY OF CHAR);
VAR f: Files.File;  r: Files.Rider;  i: INTEGER;
BEGIN
  f := Files.Old("panda.init");
  Assert(f # NIL, "Could not read panda.init.");
  Files.Set(r, f, 0);
  i := 0;
  WHILE ~r.eof DO
    Files.Read(r, s[i]);
    IF s[i] < ' ' THEN
      (* Skip to next non spacing char *)
      WHILE (~r.eof) & (s[i] <= ' ') DO Files.Read(r, s[i]) END;
    END;
    INC(i)
  END;
  s[i] := 0X
END ReadInitialText;



PROCEDURE FindTest(pattern, key: Atom): Atom;
VAR p, k: Atom; c: INTEGER;
BEGIN
  ws("FindTest, key: "); DisplayText(key); wl;
  p := pattern;  k := key;
  c := FindString(p, k);
  ws("Find count = "); wi(c); ws(", ");
  IF k = NIL THEN
    wsl("found whole key.")
  ELSIF k # key THEN
    ws("found part key up to: "); DisplayText(k); wl;
  ELSE
    wsl("key not found.")
  END;
  IF k # key THEN
    ws(".. p IS "); IF p = NIL THEN wsl("NIL.") ELSIF p IS Lnk THEN wsl("Lnk.") ELSE wsl("Val.") END;
    ws(".. found data: ");  DisplayText(p); wl
  END;
  wl;
  RETURN p
END FindTest;


PROCEDURE Test;
VAR
  Root, TestRoot, TestKey, Programs, Data, pattern, p, key, k: Atom;
  Init:  ARRAY 1000 OF CHAR;
BEGIN
  ReadInitialText(Init);
  Root := AddText(Init);
  DisplayText(Root); wl;

  Programs := FindTest(Root, AddText("root.program."));
  Programs := FindTest(Root, AddText("root.prong."));
  Programs := FindTest(Root, AddText("root.program2."));
  Programs := FindTest(Root, AddText("root.prong2."));
  Programs := FindTest(Root, AddText("root.splunge."));
  Programs := FindTest(Root, AddText("root.program.e/"));
  Data     := FindTest(Root, AddText("root.data."));
  Data     := FindTest(Root, AddText("root.da"));
  Data     := FindTest(Root, AddText("root.data.fred"));
  Data     := FindTest(Root, AddText("root.data.test:"));
  Data     := FindTest(Root, AddText("root.fred."));
  Data     := FindTest(Root, AddText("root.fred.bert.george:"));
  Data     := FindTest(Root, AddText("root.fred.harry.george:"));
  Data     := FindTest(Root, AddText("root.fred.har.george:"));
END Test;

BEGIN
  Abort:=FALSE;
  Test;
  wfl;
END panda.

--------------------------------------------------------------------------------

TODO

Not handling string continuing after alternates match?