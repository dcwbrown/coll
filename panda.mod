MODULE panda;  (* panda - programs and nested data *)

IMPORT Strings, Files, TextWriter, SYSTEM;

TYPE
  Atom   = POINTER TO AtomRec;  AtomRec = RECORD next: Atom END;
  Func   = PROCEDURE();

  Word = POINTER TO WordRec;  WordRec = RECORD (AtomRec) word: INTEGER END;
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
VAR word: Word;
BEGIN
  NEW(word);  word.word := ORD(ch);
  state.curr.next := word;
  state.curr := word;
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
    ELSIF a IS Word THEN ws(": Word")
    ELSIF a IS Atom THEN ws(": Atom")
    ELSE ws(": unknown") END;
    wfl;
  END;
END wt;

PROCEDURE OpenNest(VAR state: AddState);
VAR link: Link;
BEGIN
  NEW(link);
  link.next := state.stack;
  link.link := state.first;
  state.stack := link;
  NEW(link); link.next := state.stack; link.link := state.curr;  state.stack := link;
  NEW(state.first); state.curr := state.first;
END OpenNest;

PROCEDURE CloseNest(VAR state: AddState);
VAR link: Link;
BEGIN
  NEW(link);
  link.link := state.first.next;
  state.stack.link.next := link;
  state.curr := link;
  state.stack := state.stack.next(Link);
  state.first := state.stack.link;
  IF state.stack.next = NIL THEN
    state.stack := NIL
  ELSE
    state.stack := state.stack.next(Link)
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
    IF    a IS Word THEN wc(CHR(a(Word).word))
    ELSIF a IS Link THEN wc('['); DisplayText(a(Link).link); wc(']')
    END;
    a := a.next;
  END
END DisplayText;


(* ------------------------------ Core engine ------------------------------- *)

PROCEDURE FindString(VAR p, k: Atom): INTEGER;
VAR p2, p3, k2: Atom; c1, c2: INTEGER;
BEGIN c1 := 0;
  WHILE (p # NIL) & (k # NIL) DO
    Assert(k IS Word, "k must be Word in FindString");
    IF p IS Word THEN
      IF p(Word).word = k(Word).word THEN
        p := p.next;
        k := k.next;
        INC(c1)
      ELSE
        RETURN c1
      END
    ELSIF p IS Link THEN
      p2 := p(Link).link;
      WHILE p2 # NIL DO
        Assert(p2 IS Link, "pattern must be Link in Alternate");
        k2 := k;
        p3 := p2(Link).link;
        c2 := FindString(p3, k2);
        IF c2 > 0 THEN
          p := p3;  k := k2;  p2 := NIL
        ELSE
          p2 := p2.next
        END
      END;
      RETURN c1 + c2
    ELSE
      Fail("p neither Word nor Link in FindString.")
    END
  END;
RETURN c1 END FindString;


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
    ws(".. p IS "); IF p = NIL THEN wsl("NIL.") ELSIF p IS Link THEN wsl("Link.") ELSE wsl("Word.") END;
    ws(".. found data: ");  DisplayText(p); wl
  END;
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
  Programs := FindTest(Root, AddText("root.splunge."));
  Programs := FindTest(Root, AddText("root.program.e/"));
  Data     := FindTest(Root, AddText("root.data."));
  Data     := FindTest(Root, AddText("root.da"));
  Data     := FindTest(Root, AddText("root.data.fred"));
  Data     := FindTest(Root, AddText("root.data.test:"));
END Test;

BEGIN
  Abort:=FALSE;
  Test;
  wfl;
END panda.

--------------------------------------------------------------------------------

TODO

Not handling string continuing after alternates match?