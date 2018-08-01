MODULE das;  (* das - data, algorithms and storage *)

IMPORT Strings, Files, TextWriter, SYSTEM;

TYPE
  Atom  = POINTER TO AtomRecord;  AtomRecord  = RECORD next: Atom END;
  Value = POINTER TO ValueRecord; ValueRecord = RECORD (AtomRecord) value: LONGINT END;
  Link  = POINTER TO LinkRecord;  LinkRecord  = RECORD (AtomRecord) link:  Atom END;

  MatchState = POINTER TO MatchStateRecord;  MatchStateRecord = RECORD
    isSequence:  BOOLEAN;
    current:     Atom;
    input:       Atom;
    prevState:   MatchState;
  END;


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
  State:        MatchState;

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
PROCEDURE wb(b: BOOLEAN);        BEGIN IF b THEN ws("TRUE") ELSE ws("FALSE") END END wb;


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


(* -------------------------------- Matching ------------------------------ *)

PROCEDURE MakeMatchState(prevState: MatchState; input, pattern: Atom): MatchState;
VAR state: MatchState;
BEGIN
  Assert(pattern IS Value, "Nested match list must start with value");
  NEW(state);
  state.prevState  := prevState;
  state.input      := input;
  state.isSequence := pattern(Value).value = ORD('&');
  state.current    := pattern.next;
RETURN state END MakeMatchState;

PROCEDURE Backtrack(VAR state: MatchState; matched: BOOLEAN);
BEGIN
  IF state.prevState = NIL THEN (* Exit from entire match *)
    state.isSequence := matched;
    state := NIL
  ELSE
    IF matched THEN state.prevState.input := state.input END;
    state := state.prevState;
    IF matched = state.isSequence THEN
      state.current := state.current.next;
    ELSE (* Failure during sequence, or success of a choice *)
      Backtrack(state, matched)
    END
  END
END Backtrack;

PROCEDURE MatchStep(VAR state: MatchState);
VAR equal: BOOLEAN;
BEGIN
  IF state.current = NIL THEN  (* Reached end of list *)
    Backtrack(state, state. isSequence)
  ELSIF state.current IS Link THEN
    state := MakeMatchState(state, state.input, state.current(Link).link)
  ELSE  (* state.current IS Value *)
    equal := state.current(Value).value = state.input(Value).value;
    IF equal THEN state.input := state.input.next END;
    IF state.isSequence = equal THEN  (* move to next in list *)
      state.current := state.current.next;
    ELSE  (* look no further in list *)
      Backtrack(state, equal)
    END
  END
END MatchStep;


(* ----------------------------- Test harness ----------------------------- *)

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

PROCEDURE TestNesting;
BEGIN
  Root := CharsToList("* '[=?[ ']=?] n eu");
  Previous := Root;  WHILE Previous.next # NIL DO Previous := Previous.next END;
  Input := CharsToList("`[Testing]`[more]`.`[`x`] [`[nested]]");
  Previous.next := Input;
  Program := Root;
  WHILE Program # NIL DO Step END;
END TestNesting;

PROCEDURE NestedCharsToList(s: ARRAY OF CHAR): Atom;
VAR l, p: Atom;
BEGIN
  NEW(l);
  l.next := CharsToList(s);
  Program := CharsToList("* '[=?[ ']=?] n eu");
  Previous := l;
  Input := l.next;
  WHILE Program # NIL DO Step END;
  RETURN l.next
END NestedCharsToList;

PROCEDURE DumpState(state: MatchState);
BEGIN
  wsl("MatchState:");
  ws("  isSequence: "); wb(state.isSequence); wl;
  ws("  current:    "); wa(state.current); wl;
  ws("  input:      "); wa(state.input); wl;
END DumpState;

PROCEDURE TestMatch(expect: BOOLEAN; i, p: ARRAY OF CHAR);
VAR state, startstate: MatchState;  input, pattern: Atom;
BEGIN
  ws("Test match input '"); ws(i); ws("', pattern '"); ws(p); wsl("'.");
  input      := CharsToList(i);
  pattern    := NestedCharsToList(p);
  state      := MakeMatchState(NIL, input, pattern);
  startstate := state;
  WHILE state # NIL DO DumpState(state); MatchStep(state) END;
  ws("Matched: "); wb(startstate.isSequence); wsl(".");
  Assert(startstate.isSequence = expect, ".. expected opposite.");
  wl;
END TestMatch;

PROCEDURE TestMatching();
VAR state, startstate: MatchState;  input, pattern: Atom;
BEGIN
  TestMatch(TRUE,  "test", "&test");
  TestMatch(FALSE, "test", "&toast");
  TestMatch(TRUE,  "t", "|tuv");
  TestMatch(TRUE,  "t", "|rst");
  TestMatch(FALSE, "t", "|abc");
  TestMatch(TRUE,  "fred", "|[&bert][&fred][&harry]");
  TestMatch(TRUE,  "fred", "&fr[|aeiou]d")
END TestMatching;



BEGIN TestNesting; TestMatching
END das.
