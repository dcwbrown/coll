MODULE das;  (* das - data, algorithms and storage *)

IMPORT Strings, Files, TextWriter, SYSTEM;

TYPE
  Atom  = POINTER TO AtomRecord;  AtomRecord  = RECORD next: Atom END;
  Value = POINTER TO ValueRecord; ValueRecord = RECORD (AtomRecord) value: LONGINT END;
  Link  = POINTER TO LinkRecord;  LinkRecord  = RECORD (AtomRecord) link:  Atom END;

VAR
  Abort: BOOLEAN;

(* ---------------------- Current match/execution state --------------------- *)

  Input:        Atom;  (* Current input position *)
  Previous:     Atom;  (* Previous input position. Previous.next usually = Input *)
  Program:      Atom;  (* Current program position (intrinsic or link) *)
  ProgramStack: Link;
  LocalStack:   Link;  (* Local stack *)
  LoopStack:    Link;
  Root:         Atom;  (* Root of globa store *)
  (*
  Store:        Atom;  ( * Current position in store e.g.during a search * )
  *)

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


(* ----------------------------- Test harness ----------------------------- *)

PROCEDURE DebugChar(c: LONGINT);
BEGIN
  IF c = 10 THEN wl
  ELSIF (c >= 32) & (c < 127) THEN
    wc(CHR(c))
  ELSE
    wc('<'); wx(c,1); wc('>')
  END
END DebugChar;

PROCEDURE DebugOut(a: Atom);
BEGIN
  IF a = NIL THEN ws("<NIL>")
  ELSIF a IS Value THEN DebugChar(a(Value).value)
  ELSE
    a := a(Link).link;
    wc('{');
    WHILE a # NIL DO DebugOut(a); a := a.next END;
    wc ('}')
  END
END DebugOut;

PROCEDURE wa(a: Atom);
BEGIN
  IF a = NIL THEN ws("NIL."); wfl
  ELSIF a IS Value THEN ws("value '"); DebugChar(a(Value).value); ws("'."); wfl
  ELSE ws("link "); DebugOut(a); wc('.'); wfl
  END
END wa;

PROCEDURE CharsToList(s: ARRAY OF CHAR): Atom;
VAR first,last,new: Value; i: INTEGER;
BEGIN i := 0;
  IF (i < LEN(s)) & (s[0] # 0X) THEN
    NEW(first);  first.value := ORD(s[0]);  INC(i);
    last := first;
    WHILE (i < LEN(s)) & (s[i] # 0X) DO
      NEW(new);  new.value := ORD(s[i]);
      INC(i);  last.next := new;  last := new;
    END
  END;
RETURN first END CharsToList;


(* --------------------------------- das ---------------------------------- *)

PROCEDURE PushAtom(VAR stack: Link; a: Atom);
VAR l: Link;
BEGIN NEW(l);  l.link := a;  l.next := stack;  stack := l
END PushAtom;

PROCEDURE PushValue(VAR stack: Link; i: LONGINT);
VAR v: Value;
BEGIN NEW(v);  v.value := i;  PushAtom(stack, v)
END PushValue;

PROCEDURE PushBoolean(VAR stack: Link; b: BOOLEAN);
BEGIN IF b THEN PushValue(stack, 1) ELSE PushValue(stack, 0) END
END PushBoolean;

PROCEDURE Drop(VAR stack: Link);
BEGIN
  IF stack.next = NIL THEN stack := NIL
  ELSE stack := stack.next(Link) END;
END Drop;

PROCEDURE Pop(VAR stack: Link): Atom;
VAR a: Atom;
BEGIN a := stack.link; Drop(stack);
RETURN a END Pop;

PROCEDURE IsTrueAtom(a: Atom): BOOLEAN;
BEGIN
  IF a = NIL THEN RETURN FALSE END;
  IF a IS Link THEN RETURN a(Link).link # NIL END;
  RETURN a(Value).value # 0
END IsTrueAtom;

PROCEDURE AreEqualAtoms(a1, a2: Atom): BOOLEAN;
BEGIN
  IF a1 IS Link THEN
    RETURN (a2 IS Link) & (a1(Link).link = a2(Link).link)
  ELSE
    RETURN (a2 IS Value) & (a1(Value).value = a2(Value).value)
  END
END AreEqualAtoms;

PROCEDURE Step;
VAR intrinsic: LONGINT; l: Link; a: Atom;
BEGIN
  Assert(Program # NIL, "Program must be non-nil at start of Step.");
  IF Program IS Value THEN
    intrinsic := Program(Value).value;  Program := Program.next;
    CASE CHR(intrinsic) OF
      " ": (* No op   *)
    | "'": (* Literal *) PushAtom(LocalStack, Program);  Program := Program.next
    | "=": (* IsEqual *) PushBoolean(LocalStack, AreEqualAtoms(Input, Pop(LocalStack)))
    | '?': (* If      *) IF ~IsTrueAtom(Pop(LocalStack)) THEN Program := Program.next END
    | '[': (* Open    *) NEW(l);  l.link := Input.next;  l.next := Input.next;
                         Previous.next := l;  PushAtom(LocalStack, l)
    | ']': (* Close   *) Previous.next := NIL;  a := Pop(LocalStack);  a.next := Input.next;  Input := a
    | '*': (* Loop    *) PushAtom(LoopStack, Program)
    | 'n': (* Next    *) Assert(Input # NIL, "Next: Input cannot be NIL."); Previous := Input;  Input := Input.next
    | 'e': (* Eof     *) PushBoolean(LocalStack, Input = NIL)
    | 'u': (* Until   *) IF IsTrueAtom(Pop(LocalStack)) THEN Drop(LoopStack)
                         ELSE Program := LoopStack.link END
    | '`': (* Debug   *) DebugOut(Program);  wl;  Program := Program.next
    ELSE Fail("Unrecognised intrinsic code.")
    END
  ELSE  (* handle program link - i.e. call linked program *)
    PushAtom(ProgramStack, Program.next);
    Program := Program(Link).link
  END;
  (* Program = NIL if we've reached end of a function, return to caller *)
  WHILE (Program = NIL) & (ProgramStack # NIL) DO
    Program := ProgramStack.link;  Drop(ProgramStack);
  END
END Step;



(* ----------------------------- Test harness ----------------------------- *)

PROCEDURE Test;
BEGIN
  Root := CharsToList("* '[=?[ ']=?] n eu");
  Previous := Root;  WHILE Previous.next # NIL DO Previous := Previous.next END;
  Input := CharsToList("`[Testing]`[more]`.`[`x`] [`[nested]]");
  Previous.next := Input;
  Program := Root;
  WHILE Program # NIL DO Step END;
END Test;




BEGIN Test
END das.









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
    IF    a IS Value THEN wc(CHR(a(Value).value))
    ELSIF a IS Link THEN wc('['); DisplayText(a(Link).link); wc(']')
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
    Assert(k IS Value, "k must be Value in FindString");
    IF p IS Value THEN
      IF p(Value).value = k(Value).value THEN
        p := p.next;
        k := k.next;
        INC(count)
      ELSE
        RETURN count
      END
    ELSIF p IS Link THEN
      p2 := p(Link).link;
      pbest := NIL;  kbest := NIL;  cbest := 0;
      WHILE p2 # NIL DO
        Assert(p2 IS Link, "pattern must be Link in Alternate");
        ptest := p2(Link).link;
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
      Fail("p neither Value nor Link in FindString.")
    END
  END;
RETURN count END FindString;


PROCEDURE FindPrefix(VAR p, k: Atom): INTEGER;
VAR plnk, klnk, pnxt, knxt: Atom; clnk, cnxt: INTEGER;
BEGIN
  IF (p = NIL) OR (k = NIL) THEN RETURN 0 END;
  Assert(k IS Value, "k must be Value in FindPrefix");

  IF p IS Value THEN
    IF p(Value).value = k(Value).value THEN
      p := p.next;  k := k.next;  RETURN FindPrefix(p, k) + 1;
    ELSE
      RETURN 0
    END
  ELSIF p IS Link THEN
    (* Choose longer match of next or link fields. *)
    plnk := p(Link).link;  klnk := k;  clnk := FindPrefix(plnk, klnk);
    pnxt := p.next;      knxt := k;  cnxt := FindPrefix(pnxt, knxt);
    IF clnk > cnxt THEN
      k := klnk;  p := plnk;  RETURN clnk
    ELSIF cnxt > 0 THEN
      k := knxt;  p := pnxt;  RETURN cnxt
    ELSE
      RETURN 0
    END
  ELSE
    Fail("p is neither Value nor Link in FindPrefix.");
  END;
RETURN 0 END FindPrefix;

(* -------------------------------- Machine --------------------------------- *)

(*
  Context stack pops in this order
    1) Saved input position
    2) Program position to restore on failure
    3) Program position to restore on success
*)

PROCEDURE Failure;  (* Backup to previous program position *)
BEGIN
  Input   := Context(Link).link;  Context := Context.next;
  Program := Context(Link).link;  Context := Context.next.next;
END Failure;

PROCEDURE MatchAtom;
BEGIN
  IF Program IS Value THEN
    Assert(Input IS Value, "Input must be value.");
    IF Program(Value).value = Input(Value).value THEN
      Input := Input.next;  Program = Program.next
    ELSE
      Failure
    END
  ELSE
    Assert(Program IS Link, "Program must be Value or Link.");
    IF Program(Link).link IS Value THEN
      (* Execute list starting at Program.link *)
      Enter(Program.next, ?, Input, 1);  Program := Progam(Link).link
    ELSE
      (* recursively test alternatives at Program.link.next and
          Program.link.link.next *)

    END
  END
END MatchAtom;

(* -------------------------------- Startup --------------------------------- *)

PROCEDURE ReadInitialText(VAR s: ARRAY OF CHAR);
VAR f: Files.File;  r: Files.Rider;  i: INTEGER;
BEGIN
  f := Files.Old("das.init");
  Assert(f # NIL, "Could not read das.init.");
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
  (*c := FindString(p, k);*)
  c := FindPrefix(p, k);
  ws("Find count = "); wi(c); ws(", ");
  IF k = NIL THEN
    wsl("found whole key.")
  ELSIF k # key THEN
    ws("found part key up to: "); DisplayText(k); wl;
  ELSE
    wsl("key not found.")
  END;
  IF k # key THEN
    ws(".. p IS "); IF p = NIL THEN wsl("NIL.") ELSIF p IS Link THEN wsl("Link.") ELSE wsl("Value.") END;
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
  Programs := FindTest(Root, AddText("root.program.s/"));
  Data     := FindTest(Root, AddText("root.data."));
  Data     := FindTest(Root, AddText("root.da"));
  Data     := FindTest(Root, AddText("root.data.fred"));
  Data     := FindTest(Root, AddText("root.data.test:"));
  Data     := FindTest(Root, AddText("root.fred."));
  Data     := FindTest(Root, AddText("root.fred.bert.george:"));
  Data     := FindTest(Root, AddText("root.fred.harry.george:"));
  Data     := FindTest(Root, AddText("root.fred..george:"));
  Data     := FindTest(Root, AddText("root.fred.har.george:"));
END Test;

BEGIN
  Abort:=FALSE;
  Test;
  wfl;
END das.

--------------------------------------------------------------------------------

