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

PROCEDURE ^FindString(VAR pattern, key: Atom): BOOLEAN;


PROCEDURE Interpret(VAR pattern, key: Atom): BOOLEAN;
VAR  c: CHAR;  p, p2, k, k2: Atom;
BEGIN (*wsl("Interpret.");*)
  p := pattern;  k := key;  c := '/';
  IF p IS Word THEN
    c := CHR(p(Word).word);
    p := p.next;
  END;
  Assert(c = '/', "Only know how to interpret alternates.");
  WHILE p # NIL DO
    Assert(p IS Link, "pattern must be Link in Interpret");
    k2 := k;
    p2 := p(Link).link;
    IF FindString(p2, k2) THEN
      pattern := p2;  key := k2;
      RETURN TRUE
    END;
    p := p.next
  END;
RETURN FALSE END Interpret;


PROCEDURE FindString(VAR pattern, key: Atom): BOOLEAN;
VAR p, p2, k, k2: Atom;
BEGIN
  p := pattern;  k := key;
  WHILE (p # NIL) & (k # NIL) DO
    Assert(k IS Word, "k must be Word in FindString");
    IF p IS Word THEN
      IF p(Word).word = k(Word).word THEN
        p := p.next;
        k := k.next;
      ELSE
        RETURN FALSE
      END
    ELSIF p IS Link THEN
      p2 := p(Link).link;  k2 := k;
      IF ~Interpret(p2, k2) THEN RETURN FALSE END;
      IF k2 = NIL THEN pattern := p2; key := NIL; RETURN TRUE END;
      p := p.next
    ELSE
      Fail("p neither Word nor Link in FindString.")
    END
  END;
  IF k = NIL THEN pattern := p;  key := NIL END;
RETURN k = NIL END FindString;





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


PROCEDURE Test;
VAR
  Root, TestRoot, TestKey, Programs, Data, pattern, key: Atom;
  Init:  ARRAY 1000 OF CHAR;
BEGIN
  DisplayText(AddText("The ^^cat sat [on the] mat.")); wl;

  (*Root := AddText("/['root.[/['program.[/['e/[!emphasize]]['s/[strengthen]]]]['data[Hello [e/muchly] dave.]]]]");*)
  ReadInitialText(Init);
  Root := AddText(Init);
  DisplayText(Root); wl;

  pattern := Root;
  key     := AddText("root.program.");

  IF FindString(pattern, key) THEN
    Assert(pattern # NIL, "FindString returned pattern not expected to be NIL.");
    Programs := pattern(Link).link;
    ws("Found programs: ");  DisplayText(Programs); wl;
    pattern := Root;
    key     := AddText("root.data.");
    IF FindString(pattern, key) THEN
      Data := pattern(Link).link;
      ws("Found data: ");  DisplayText(Data); wl;
    ELSE
      wsl("'root.data' Not found.")
    END;
  ELSE
    wsl("'root.program.'' Not found.")
  END
END Test;

BEGIN
  Abort:=FALSE;
  Test;
  wfl;
END panda.

--------------------------------------------------------------------------------

TODO
Match as mutch as possible and return pattern from that point. E.g. need to
be able to match the 'e/' in 'e/muchly'.
