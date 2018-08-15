MODULE dam;  (* dam - data, algorithms and memory *)

IMPORT Strings, Files, TextWriter, SYSTEM;

TYPE
  Address = SYSTEM.ADDRESS;
  AtomPtr = POINTER [1] TO Atom;
  Atom = RECORD
    next: Address;  (* Bottom bit of next determines use of value below *)
    data: Address   (* next MOD 2 = 0: integer value, 1: link address *)
  END;


VAR
  Abort:  BOOLEAN;
  Memory: ARRAY 1000 OF Atom;
  Free:   AtomPtr;

  LocalStack:    AtomPtr;
  Program:       AtomPtr;
  ProgramStack:  AtomPtr;
  LoopStack:     AtomPtr;
  Boot:          AtomPtr;

  (* Standard global variables *)
  Input:         AtomPtr;
  Pattern:       AtomPtr;
  Sequence:      AtomPtr;
  MatchFn:       AtomPtr;
  BacktrackFn:   AtomPtr;

  IntrinsicVariable: ARRAY 26 OF AtomPtr;

(* ---------------------- Current match/execution state --------------------- *)


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

PROCEDURE DebugChar(c: LONGINT);
BEGIN
  IF c = 10 THEN wl
  ELSIF (c >= 32) & (c < 127) THEN
    wc(CHR(c))
  ELSE
    wc('<'); wx(c,1); wc('>')
  END
END DebugChar;


(* ----------------------------- Atom access ------------------------------ *)

PROCEDURE BoolVal(b: BOOLEAN): Address;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE IsValue(a: AtomPtr): BOOLEAN;
BEGIN RETURN (a.next MOD 2) = 0 END IsValue;

PROCEDURE Next(a: AtomPtr): AtomPtr;
BEGIN RETURN SYSTEM.VAL(AtomPtr, (a.next DIV 2) * 2) END Next;

PROCEDURE Value(a: AtomPtr): Address;
BEGIN Assert(a.next MOD 2 = 0, "Cannot get value from atom that is a link.");
RETURN a.data END Value;

PROCEDURE Link(a: AtomPtr): AtomPtr;
BEGIN
  IF a.next MOD 2 # 1 THEN
    ws("Get link from value '"); DebugChar(Value(a)); wsl("'.");
  END;
  Assert(a.next MOD 2 = 1, "Cannot get link from atom that is a value.");
RETURN SYSTEM.VAL(AtomPtr, a.data) END Link;

PROCEDURE SetNext(a, b: AtomPtr);
BEGIN a.next := SYSTEM.VAL(Address, b) + a.next MOD 2
END SetNext;

PROCEDURE SetValue(a: AtomPtr; b: Address);
BEGIN
  a.data := b;  DEC(a.next, a.next MOD 2)  (* Turn off link flag *)
END SetValue;

PROCEDURE SetLink(a, b: AtomPtr);
BEGIN
  a.data := SYSTEM.VAL(Address, b);
  IF IsValue(a) THEN INC(a.next) END  (* Turn on link flag *)
END SetLink;

PROCEDURE NewAtom(): AtomPtr;
VAR result: AtomPtr;
BEGIN
  Assert(Free # NIL, "Out of memory.");
  result := Free;  Free := Next(Free);
  result.next := 0;  result.data := 0;
RETURN result END NewAtom;

PROCEDURE FreeAtom(a: AtomPtr);
BEGIN
  a.next := SYSTEM.VAL(Address, Free);
  a.data := 0;
  Free := a
END FreeAtom;

PROCEDURE InitMemory;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO LEN(Memory)-2 DO
    Memory[i].next := SYSTEM.ADR(Memory[i+1]);
    Memory[i].data := 0;
  END;
  Memory[LEN(Memory)-1].next := 0;
  Memory[LEN(Memory)-1].data := 0
END InitMemory;


(* ----------------------------- Test harness ----------------------------- *)

PROCEDURE^ DebugOut(a: AtomPtr);

PROCEDURE DumpList(a: AtomPtr);
BEGIN
    wc('{');
    WHILE a # NIL DO DebugOut(a); a := Next(a) END;
    wc ('}')
END DumpList;

PROCEDURE DebugOut(a: AtomPtr);
BEGIN
  IF a = NIL THEN ws("<NIL>")
  ELSIF IsValue(a) THEN DebugChar(Value(a))
  ELSE DumpList(Link(a))
  END
END DebugOut;

PROCEDURE wa(a: AtomPtr);
BEGIN
  IF a = NIL THEN ws("NIL."); wfl
  ELSIF IsValue(a) THEN ws("value '"); DebugChar(Value(a)); ws("'."); wfl
  ELSE ws("link "); DebugOut(a); wc('.'); wfl
  END
END wa;


(* -------------------------------- Stacks -------------------------------- *)

PROCEDURE CopyAtom(source, target: AtomPtr);
BEGIN
  (*ws("Copy atom. Source: "); wa(source); ws(", Target: "); wa(target); wsl(".");*)
  target.data := source.data;
  target.next  := (target.next DIV 2) * 2 + source.next MOD 2
END CopyAtom;

PROCEDURE PushAtom(VAR stack: AtomPtr;  a: AtomPtr);
VAR l: AtomPtr;
BEGIN l := NewAtom();
  l.next := a.next;  l.data := a.data;
  SetNext(l, stack);  stack := l
END PushAtom;

PROCEDURE PushLink(VAR stack: AtomPtr;  l: AtomPtr);
VAR a: AtomPtr;
BEGIN a := NewAtom();
  SetNext(a, stack);  SetLink(a, l);  stack := a
END PushLink;

PROCEDURE PushValue(VAR stack: AtomPtr; v: Address);
VAR l: AtomPtr;
BEGIN l := NewAtom();  SetValue(l, v);  SetNext(l, stack);  stack := l
END PushValue;

PROCEDURE Drop(VAR stack: AtomPtr);
VAR unwanted: AtomPtr;
BEGIN unwanted := stack;  stack := Next(stack);  FreeAtom(unwanted)
END Drop;

PROCEDURE PopLink(VAR stack: AtomPtr): AtomPtr;
VAR result: AtomPtr;
BEGIN Assert(~IsValue(stack), "Cannot pop link when top of stcak is value.");
  result := Link(stack);  Drop(stack);
RETURN result END PopLink;


(* ---------------------- Intrinsic variables (a..z) ---------------------- *)


PROCEDURE MakeIntrinsicVariables;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO 25 DO IntrinsicVariable[i] := NewAtom() END;
  Input       := IntrinsicVariable[ORD('i')-ORD('a')];
  Pattern     := IntrinsicVariable[ORD('p')-ORD('a')];
  Sequence    := IntrinsicVariable[ORD('s')-ORD('a')];
  MatchFn     := IntrinsicVariable[ORD('m')-ORD('a')];
  BacktrackFn := IntrinsicVariable[ORD('b')-ORD('a')];
END MakeIntrinsicVariables;

(* ---------------------------- Atom functions ---------------------------- *)


(* ----------------------------- Interpreter ------------------------------ *)

PROCEDURE Step;
VAR intrinsic: Address;  a, n: AtomPtr;
BEGIN
  Assert(Program # NIL, "Program must be non-nil at start of Step.");
  n := Next(Program);
  IF IsValue(Program) THEN
    intrinsic := Value(Program);
    (*ws("Intrinsic '"); wc(CHR(intrinsic)); wsl("'.");*)
    CASE CHR(intrinsic) OF
    |' ', 0AX, 0DX: (* No op   *)

    (* Intrinsic global variables *)
    |'a'..'z':         PushLink(LocalStack, IntrinsicVariable[intrinsic - ORD('a')])

    (* Stack manipulation *)
    |'%':(* Dup     *) PushAtom(LocalStack, LocalStack)
    |'#':(* Drop    *) Drop(LocalStack)

    (* Literals *)
    |'0':(* Zero    *) PushValue(LocalStack, 0)
    |'1':(* One     *) PushValue(LocalStack, 1)
    |"'":(* Literal *) PushAtom(LocalStack, n);  n := Next(n)

    (* Basic operations *)
    |'~':(* Not     *) LocalStack.data := BoolVal(LocalStack.data = 0)
    |'=':(* Equal   *) a := Next(LocalStack);
                       SetValue(a, BoolVal(
                           (IsValue(LocalStack) = IsValue(a))
                         & (LocalStack.data     = (a.data))));
                       Drop(LocalStack)
    |'&':(* And     *) a := Next(LocalStack);
                       SetValue(a, BoolVal((LocalStack.data#0) & (a.data#0)));
                       Drop(LocalStack)

    (* Conditionals and loops *)
    |'?':(* If      *) IF LocalStack.data = 0 THEN
                         n := Next(n);
                         IF IsValue(n) & (Value(n) = ORD('\')) THEN n := Next(n) END
                        END;
                       Drop(LocalStack)
    |'\':(* else    *) n := Next(n)

    (* Atom access *)
    |'_':(* is Link *) SetValue(LocalStack, BoolVal(~IsValue(LocalStack)))
    |',':(* Next    *) SetLink(LocalStack, Next(Link(LocalStack)))
    |'.':(* Fetch   *) CopyAtom(Link(LocalStack), LocalStack)
    |':':(* Store   *) CopyAtom(Next(LocalStack), Link(LocalStack));
                       Drop(LocalStack);  Drop(LocalStack)
    |'!':(* Execute *) PushLink(ProgramStack, n); n := PopLink(LocalStack)

    |'$':(* Debug   *) DebugOut(LocalStack);  wl;  Drop(LocalStack);
    ELSE wlc; wi(intrinsic); wc(' '); DebugChar(intrinsic); wc(' ');
      Fail("Unrecognised intrinsic code.")
    END;
    Program := n
  ELSE  (* handle program link - i.e. call linked program *)
    IF Link(Program) = NIL THEN
      Program := n
    ELSE
      PushLink(ProgramStack, n);
      Program := Link(Program)
    END
  END;
  (* Program = NIL if we've reached end of a function, return to caller *)
  WHILE (Program = NIL) & (ProgramStack # NIL) DO Program := PopLink(ProgramStack) END
END Step;



(* -------------------------------- Matching ------------------------------ *)

PROCEDURE InitMatchList(pattern: AtomPtr);
(* p.. %,p! .''=s! *)
BEGIN
  SetValue(Sequence, BoolVal(Value(pattern) = ORD("'")));
  Pattern := Next(pattern);
END InitMatchList;

PROCEDURE Backtrack(matched: BOOLEAN);
(*  *)
VAR prevInput: AtomPtr;
BEGIN
  IF Link(LocalStack) = NIL THEN  (* Pattern is complete *)
    Drop(LocalStack); PushValue(LocalStack, BoolVal(matched)); Pattern := NIL
  ELSE
    Pattern := PopLink(LocalStack);
    IF matched THEN Drop(LocalStack) ELSE SetLink(Input, PopLink(LocalStack)) END;
    Assert(IsValue(LocalStack), "Expected Saved Sequence value on local stack.");
    SetValue(Sequence, Value(LocalStack));  Drop(LocalStack);
    IF matched = (Value(Sequence)#0) THEN
      Pattern := Next(Pattern)
    ELSE (* Failure during sequence, or success of a choice *)
      Backtrack(matched)
    END
  END
END Backtrack;

PROCEDURE MatchStep;
(*
  p.._?[ `[Pattern entry is link]
    s. i. p.  `[Push sequence flag, input position and pattern position on local stack]
    p.. %,p! .''=s!  `[Initialise match in nested list]
  ][     `[Pattern entry is value]
    p.. i.. =
    %?[i.,i.:]
    % s.= p., & ?[#p.,p:]\[b!]
  ]
*)
VAR equal: BOOLEAN;
BEGIN
  Assert(Pattern # NIL, "MatchStep entered with unexpectedly NIL pattern.");
  IF IsValue(Pattern) THEN
    equal := Value(Pattern) = Value(Link(Input));
    IF equal THEN SetLink(Input, Next(Link(Input))) END;
    IF ((Value(Sequence)#0) = equal) & (Next(Pattern) # NIL) THEN  (* move to next in list *)
      Pattern := Next(Pattern)
    ELSE  (* look no further in list *)
      Backtrack(equal)
    END
  (*
  ELSIF Link(Pattern) = NIL THEN
    Pattern := Next(Pattern);
    IF Pattern = NIL THEN Backtrack(Value(Sequence)#0) END
  *)
  ELSE
    PushValue(LocalStack, Value(Sequence));
    PushLink(LocalStack, Link(Input));
    PushLink(LocalStack, Pattern);
    InitMatchList(Link(Pattern))
  END;
END MatchStep;

PROCEDURE StartMatch(pattern: AtomPtr);
BEGIN
  PushLink(LocalStack, NIL);
  InitMatchList(pattern)
END StartMatch;


(* ------------------------------- Bootstrap -------------------------------- *)

PROCEDURE BootstrapAddChar(VAR current: AtomPtr;  VAR escaped: BOOLEAN;  ch: CHAR);
VAR nest: AtomPtr;
BEGIN
  IF escaped THEN
    SetNext(current, NewAtom());  current := Next(current);  SetValue(current, ORD(ch));
    escaped := FALSE
  ELSE
    CASE ch OF
    |'^': escaped := TRUE
    |'[': SetNext(current, NewAtom());  current := Next(current);  PushLink(LocalStack, current)
    |']': nest := PopLink(LocalStack);  SetLink(nest, Next(nest));
          SetNext(current, NIL);  current := nest;  SetNext(current, NIL)
    ELSE  SetNext(current, NewAtom());  current := Next(current);  SetValue(current, ORD(ch))
    END
  END
END BootstrapAddChar;

PROCEDURE BootstrapLoader(s: ARRAY OF CHAR): AtomPtr;
VAR head, current: AtomPtr;  i: INTEGER;  escaped: BOOLEAN;
BEGIN i := 0;
  head := NewAtom();  current := head;  escaped := FALSE;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO
    BootstrapAddChar(current, escaped, s[i]);  INC(i)
  END;
  current := Next(head);  FreeAtom(head);
RETURN current END BootstrapLoader;

PROCEDURE LoadBoostrap(): AtomPtr;
VAR head, current, nest: AtomPtr;
    i:                   INTEGER;
    escaped:             BOOLEAN;
    f:                   Files.File;
    r:                   Files.Rider;
    c:                   CHAR;
BEGIN
  head := NewAtom();  current := head;  escaped := FALSE;
  f := Files.Old("dam.boot");  Assert(f # NIL, "Expected file dam.boot.");
  Files.Set(r, f, 0);  Files.Read(r, c);
  WHILE ~r.eof DO
    IF c # 0DX THEN BootstrapAddChar(current, escaped, c) END;
    Files.Read(r, c)
  END;
  current := Next(head);  FreeAtom(head);
RETURN current END LoadBoostrap;


(* ----------------------------- Test harness ----------------------------- *)

PROCEDURE TestNewAtom;
VAR i: INTEGER; p: AtomPtr;
BEGIN
  FOR i := 1 TO LEN(Memory) DO
    p := NewAtom();
    wi(i); ws(" at "); wx(SYSTEM.VAL(Address, p), 1); wl;
  END;
  wsl("Allocated LEN(Memory) atoms successfully, trying one more, which should fail with an out of memory error.");
  p := NewAtom()
END TestNewAtom;

PROCEDURE TestIntrinsicCode(s: ARRAY OF CHAR);
BEGIN
  Program := BootstrapLoader(s);
  WHILE Program # NIL DO Step END;
END TestIntrinsicCode;

PROCEDURE TestOberonCodedMatch(expect: BOOLEAN; i, p: ARRAY OF CHAR);
VAR matched: BOOLEAN;
BEGIN
  ws("Test match input '"); ws(i); ws("', pattern '"); ws(p); ws("',  ");
  StartMatch(BootstrapLoader(p));
  SetLink(Input, BootstrapLoader(i));

  WHILE Pattern # NIL DO MatchStep END;

  matched := Value(LocalStack)#0;  Drop(LocalStack);
  ws("Matched: "); wb(matched);
  Assert(matched = expect, " .. expected opposite.");
  wsl(" as expected.");
END TestOberonCodedMatch;

PROCEDURE TestOberonCodedMatching;
BEGIN
  TestOberonCodedMatch(TRUE,  "test", "'test");
  TestOberonCodedMatch(FALSE, "test", "'toast");
  TestOberonCodedMatch(TRUE,  "t",    "/tuv");
  TestOberonCodedMatch(TRUE,  "t",    "/rst");
  TestOberonCodedMatch(FALSE, "t",    "/abc");
  TestOberonCodedMatch(TRUE,  "test", "'te['s]t");
  TestOberonCodedMatch(TRUE,  "fred", "/['bert]['fred]['harry]");
  TestOberonCodedMatch(TRUE,  "fred", "'fr[/aeiou]d")
END TestOberonCodedMatching;


BEGIN
  Assert(SYSTEM.VAL(Address, NIL) = 0, "Expected NIL to be zero.");
  InitMemory;
  Free := SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory));
  (*TestNewAtom;*)
  MakeIntrinsicVariables;
  TestIntrinsicCode("'[-- Testing bootstrap nesting parser.]$ '[more]$ '.$ '[$x$]$ ['[nested]$] '[abc[def]ghi]$");
  TestOberonCodedMatching;
  TestIntrinsicCode("'[-- Testing stored programs.]$ '['[stored program]$]m: '[within]$ m!");

  Boot := LoadBoostrap();  DumpList(Boot);

  (* Run the bootstrap *)
  Program := Boot;  WHILE Program # NIL DO Step END;
END dam.

