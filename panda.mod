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

  MatchState = RECORD
    pattern: Atom;
    key:     Atom;
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

PROCEDURE MatchLiteral(VAR state: MatchState): BOOLEAN;
VAR p, k: Atom;
BEGIN
  p := state.pattern;  k := state.key;
  WHILE (p # NIL) & (p IS Word) & (k # NIL) DO
    Assert(k IS Word, "k must be Word in MatchLiteral");
    ws("MatchLiteral: p '"); wc(CHR(p(Word).word));
    ws("', k '"); wc(CHR(k(Word).word)); wsl("'.");
    IF p(Word).word = k(Word).word THEN
      p := p.next;
      k := k.next;
    ELSE
      RETURN FALSE
    END
  END;
  IF (p = NIL) OR (p IS Link) THEN (* Matched whole pattern => success *)
    state.pattern := p; state.key := k; RETURN TRUE
  ELSE (* Partial match is no match *)
    RETURN FALSE
  END
END MatchLiteral;


PROCEDURE ^FindString(VAR state: MatchState): BOOLEAN;

PROCEDURE Interpret(VAR state: MatchState): BOOLEAN;
VAR  c: CHAR;  s, s2: MatchState;
BEGIN  wsl("Interpret.");
  c := '/';  s := state;
  IF s.pattern IS Word THEN
    c := CHR(s.pattern(Word).word);
    s.pattern := s.pattern.next;
  END;
  Assert(c = '/', "Only know how to interpret alternates.");
  WHILE s.pattern # NIL DO
    Assert(s.pattern IS Link, "pattern must be Link in Interpret");
    s2.key := s.key;
    s2.pattern := s.pattern(Link).link;
    IF FindString(s2) THEN state := s2; RETURN TRUE END;
    s.pattern := s.pattern.next
  END;
RETURN FALSE END Interpret;

PROCEDURE FindString(VAR state: MatchState): BOOLEAN;
VAR s, s2: MatchState;
BEGIN wsl("FindString.");
  s := state;
  WHILE (s.pattern # NIL) & (s.key # NIL) DO
    Assert(s.key IS Word, "s.key must be Word in FindString");
    IF s.pattern IS Word THEN
      ws("FindString: s.pattern '"); wc(CHR(s.pattern(Word).word)); ws("', s.key '"); wc(CHR(s.key(Word).word)); wsl("'.");
      IF ~MatchLiteral(s) THEN RETURN FALSE END;
      ws("MatchLiteral succeeded, s.pattern is ");
      IF s.pattern # NIL THEN ws("not ") END;
      ws("NIL, s.key is ");
      IF s.key # NIL THEN ws("not ") END;
      wsl("NIL.")
    ELSIF s.pattern IS Link THEN
      ws("FindString: s.key '"); wc(CHR(s.key(Word).word)); wsl("'.");
      s2.pattern := s.pattern(Link).link;
      s2.key := s.key;
      IF ~Interpret(s2) THEN RETURN FALSE END;
      IF s2.key = NIL THEN state := s2; RETURN TRUE END;
      s.pattern := s.pattern.next
    ELSE
      Fail("s.pattern neither Word nor Link in FindString.")
    END
  END;
  IF s.key = NIL THEN state := s END;
  ws("FindString returning, state.pattern is ");
  IF state.pattern # NIL THEN ws("not ") END;
  wsl("NIL.");
RETURN s.key = NIL END FindString;


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
  Root, TestRoot, TestKey, Programs, Data: Atom;
  State: MatchState;
  Init:  ARRAY 1000 OF CHAR;
BEGIN
  DisplayText(AddText("The ^^cat sat [on the] mat.")); wl;

  (*Root := AddText("/['root.[/['program.[/['e/[!emphasize]]['s/[strengthen]]]]['data[Hello [e/muchly] dave.]]]]");*)
  ReadInitialText(Init);
  Root := AddText(Init);
  DisplayText(Root); wl;

  State.pattern := Root;
  State.key     := AddText("root.program.");

  IF FindString(State) THEN
    Assert(State.pattern # NIL, "FindString returned pattern not expected to be NIL.");
    Programs := State.pattern(Link).link;
    wsl("Found programs: ");  DisplayText(Programs); wl;
    State.pattern := Root;
    State.key     := AddText("root.data.");
    IF FindString(State) THEN
      Data := State.pattern(Link).link;
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


TODO
Match as mutch as possible and return pattern from that point. E.g. need to
be able to match the 'e/' in 'e/muchly'.
