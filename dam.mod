MODULE dam;  (* dam - data, algorithms and memory *)

IMPORT Strings, Files, TextWriter, SYSTEM, In;

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


(* ---------------------------- Unicode output ---------------------------- *)

PROCEDURE wut(u: LONGINT; n: INTEGER);
BEGIN
  IF n > 1 THEN wut(u DIV 64, n-1) END;
  wc(CHR(u MOD 64 + 080H))
END wut;

PROCEDURE wu(u: LONGINT);  (* Write Unicode codepoint as UTF-8 *)
BEGIN
  IF    u < 000080H THEN wc(CHR(u))
  ELSIF u < 000800H THEN wc(CHR(u DIV 00040H + 0C0H));  wut(u, 1)
  ELSIF u < 010000H THEN wc(CHR(u DIV 01000H + 0E0H));  wut(u, 2)
  ELSIF u < 110000H THEN wc(CHR(u DIV 40000H + 0F0H));  wut(u, 3)
  ELSE Fail("Write unicode value > 10FFFFH.")
  END
END wu;


(* ----------------------------- Atom access ------------------------------ *)

PROCEDURE BoolVal(b: BOOLEAN): Address;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE Truth(a: AtomPtr): BOOLEAN;
BEGIN RETURN a.data # 0 END Truth;

PROCEDURE IsValue(a: AtomPtr): BOOLEAN;
BEGIN RETURN (a.next MOD 2) = 0 END IsValue;

PROCEDURE Next(a: AtomPtr): AtomPtr;
BEGIN RETURN SYSTEM.VAL(AtomPtr, (a.next DIV 8) * 8) END Next;

PROCEDURE Value(a: AtomPtr): Address;
BEGIN Assert(a.next MOD 2 = 0, "Cannot get value from atom that is a link.");
RETURN a.data END Value;

PROCEDURE Link(a: AtomPtr): AtomPtr;
BEGIN
  IF a.next MOD 2 # 1 THEN
    wlc; ws("Get link from value '"); DebugChar(Value(a)); wsl("'.");
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
    wc('[');
    WHILE a # NIL DO DebugOut(a); a := Next(a) END;
    wc (']')
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

PROCEDURE PopLink(VAR stack: AtomPtr): AtomPtr;
VAR result: AtomPtr;
BEGIN Assert(~IsValue(stack), "Cannot pop link when top of stack is value.");
  result := Link(stack);  stack := Next(stack);
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

PROCEDURE WriteAtomAsChars(a: AtomPtr);
BEGIN
  IF IsValue(a) THEN
    wu(Value(a))
  ELSE
    a := Link(a);  WHILE a # NIL DO WriteAtomAsChars(a); a := Next(a) END
  END
END WriteAtomAsChars;

PROCEDURE Step;
VAR intrinsic: Address;  a, n: AtomPtr;  c: CHAR;
BEGIN
  Assert(Program # NIL, "Program must be non-nil at start of Step.");
  n := Next(Program);
  IF IsValue(Program) THEN
    intrinsic := Value(Program);
    (*ws("Intrinsic '"); wc(CHR(intrinsic)); wsl("'.");*)
    CASE CHR(intrinsic) OF
    |' ', 0AX, 0DX: (* No op   *)

    (* Intrinsic global variables a..z and integer literals 0..F *)
    |'a'..'z':         PushLink(LocalStack, IntrinsicVariable[intrinsic - ORD('a')])
    |'0'..'9':         PushValue(LocalStack, intrinsic - ORD('0'))
    |'A'..'F':         PushValue(LocalStack, intrinsic - ORD('A') + 10)
    |'`':              PushAtom(LocalStack, n);  n := Next(n)

    (* Stack manipulation *)
    |'%':(* Dup     *) PushAtom(LocalStack, LocalStack)
    |'#':(* Drop    *) LocalStack := Next(LocalStack)

    (* Basic operations *)
    |'~':(* Not     *) LocalStack.data := BoolVal(LocalStack.data = 0)
    |'=':(* Equal   *) a := Next(LocalStack);
                       SetValue(a, BoolVal(
                           (IsValue(LocalStack) = IsValue(a))
                         & (LocalStack.data     = (a.data))));
                       LocalStack := Next(LocalStack)
    |'+':(* Plus    *) a := Next(LocalStack);
                       SetValue(a, Value(LocalStack) + Value(a));
                       LocalStack := Next(LocalStack)
    |'&':(* And     *) a := Next(LocalStack);
                       SetValue(a, BoolVal((Truth(LocalStack)) & (Truth(a))));
                       LocalStack := Next(LocalStack)

    (* Conditional *)
    |'?':(* If      *) IF Truth(Next(LocalStack)) THEN
                         PushLink(ProgramStack, n);
                         n := Link(LocalStack);
                         PushLink(ProgramStack, n)
                       END;
                       LocalStack := Next(Next(LocalStack))

    (* Atom access *)
    |'_':(* is Link *) SetValue(LocalStack, BoolVal(~IsValue(LocalStack)))
    |',':(* Next    *) SetLink(LocalStack, Next(Link(LocalStack)))
    |'.':(* Fetch   *) CopyAtom(Link(LocalStack), LocalStack)
    |':':(* Store   *) CopyAtom(Next(LocalStack), Link(LocalStack));
                       LocalStack := Next(Next(LocalStack))

    (* Control transfer *)
    |'!':(* Execute *) PushLink(ProgramStack, n);
                       n := PopLink(LocalStack);
                       PushLink(ProgramStack, n)
    |'@':(* Loop    *) n := Link(ProgramStack)
    |"'":(* Exit1   *) ProgramStack := Next(ProgramStack);
                       n := Link(ProgramStack); ProgramStack := Next(ProgramStack)
    |'"':(* Exit2   *) ProgramStack := Next(ProgramStack); ProgramStack := Next(ProgramStack); ProgramStack := Next(ProgramStack);
                       n := Link(ProgramStack); ProgramStack := Next(ProgramStack)

    (* Input and output *)
    |'R':(* Input   *) In.Char(c);  PushValue(LocalStack, ORD(c))
    |'W':(* Output  *) WriteAtomAsChars(LocalStack); LocalStack := Next(LocalStack)
    |'N':(* Newline *) wl
    |'S':(* DebugOut*) DebugOut(LocalStack); wl

    ELSE wlc; wi(intrinsic); wc(' '); DebugChar(intrinsic); wc(' ');
      Fail("Unrecognised intrinsic code.")
    END
  ELSE  (* handle program link - i.e.push linked list *)
    PushAtom(LocalStack, Program)
  END;
  Program := n;
  (* When Program = NIL we've reached end of function and must return to caller *)
  WHILE (Program = NIL) & (ProgramStack # NIL) DO
    ProgramStack := Next(ProgramStack);  Program := PopLink(ProgramStack)
  END
END Step;



(* -------------------------------- Matching ------------------------------ *)

PROCEDURE InitMatchList(pattern: AtomPtr);
BEGIN
  SetValue(Sequence, BoolVal(Value(pattern) = ORD("'")));
  Pattern := Next(pattern);
END InitMatchList;

PROCEDURE Backtrack(matched: BOOLEAN);
VAR prevInput: AtomPtr;
BEGIN
  IF Link(LocalStack) = NIL THEN  (* Pattern is complete *)
    LocalStack := Next(LocalStack); PushValue(LocalStack, BoolVal(matched)); Pattern := NIL
  ELSE
    Pattern := PopLink(LocalStack);
    IF matched THEN LocalStack := Next(LocalStack) ELSE SetLink(Input, PopLink(LocalStack)) END;
    Assert(IsValue(LocalStack), "Expected Saved Sequence value on local stack.");
    SetValue(Sequence, Value(LocalStack));  LocalStack := Next(LocalStack);
    IF matched = (Value(Sequence)#0) THEN
      Pattern := Next(Pattern)
    ELSE (* Failure during sequence, or success of a choice *)
      Backtrack(matched)
    END
  END
END Backtrack;

PROCEDURE MatchStep;
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

(*
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
*)

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

  matched := Value(LocalStack)#0;  LocalStack := Next(LocalStack);
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


(* ------------------ Garbage collection experimentiation ----------------- *)

PROCEDURE Used(a: AtomPtr);
TYPE
  AtomAsSetsPtr = POINTER TO AtomAsSets;
  AtomAsSets = RECORD next, data: SET END;
VAR sp: AtomAsSetsPtr;
BEGIN
  IF (a # NIL) & ((a.next MOD 4) < 2) THEN  (* If not already marked used *)
    WHILE a # NIL DO
      IF ~IsValue(a) THEN Used(Link(a)) END;
      sp := SYSTEM.VAL(AtomAsSetsPtr, a);
      INCL(sp.next, 1);
      a := Next(a)
    END
  END
END Used;

PROCEDURE CountUsed;
TYPE
  AtomAsSetsPtr = POINTER TO AtomAsSets;
  AtomAsSets = RECORD next, data: SET END;
VAR sp: AtomAsSetsPtr;  i, used, unused, free: INTEGER;  a: AtomPtr;
BEGIN
  used := 0;  free := 0;
  FOR i := 0 TO LEN(Memory)-1 DO
    sp := SYSTEM.VAL(AtomAsSetsPtr, SYSTEM.ADR(Memory[i]));
    IF 1 IN sp^.next THEN INC(used) ELSE INC(unused) END
  END;

  a := Free;  free := 0;
  WHILE a # NIL DO
    sp := SYSTEM.VAL(AtomAsSetsPtr, a);
    Assert(~(1 IN sp.next), "Expected all free list entries to be unused.");
    INC(free); a := Next(a)
  END;

  ws("Used "); wi(used); ws(", unused "); wi(unused);
  ws(", freelist "); wi(free); ws(", collectable "); wi(unused-free);
  wsl(".")
END CountUsed;

PROCEDURE Garbage;
TYPE
  AtomAsSetsPtr = POINTER TO AtomAsSets;
  AtomAsSets = RECORD next, data: SET END;
VAR i: INTEGER; sp: AtomAsSetsPtr;
BEGIN
  wsl("Set all items garbage bit to zero.");
  FOR i := 0 TO LEN(Memory)-1 DO
    sp := SYSTEM.VAL(AtomAsSetsPtr, SYSTEM.ADR(Memory[i]));
    EXCL(sp^.next, 1)
  END;

  wsl("Mark LocalStack used.");
  Used(LocalStack);
  wsl("Mark Program used.");
  Used(Program);
  wsl("Mark ProgramStack used.");
  Used(ProgramStack);
  wsl("Mark LoopStack used.");
  Used(LoopStack);
  wsl("Mark Boot used.");
  Used(Boot);

  CountUsed
END Garbage;

BEGIN
  Assert(SYSTEM.VAL(Address, NIL) = 0, "Expected NIL to be zero.");
  InitMemory;
  Free := SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory));
  (*TestNewAtom;*)
  MakeIntrinsicVariables;

  (*
  TestIntrinsicCode("[-- Testing bootstrap nesting parser.]WL [more]WL [x]WL [[nested]WL] [abc[def]ghi]WL");
  *)

  TestOberonCodedMatching;

  (*
  TestIntrinsicCode("[-- Testing stored programs.]WL [[stored program]WL]m: [within]WL m!");
  *)

  Boot := LoadBoostrap();  (*DumpList(Boot);*)

  (* Run the bootstrap *)
  Program := Boot;  WHILE Program # NIL DO Step END;


  (* Garbage detection *)
  Garbage

END dam.

