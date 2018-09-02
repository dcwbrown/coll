MODULE dam;  (* dam - data, algorithms and memory *)

IMPORT Strings, Files, TextWriter, SYSTEM, In;

CONST
  AtomCount  = 6000;
  StackDepth = 100;
  MaxLines   = 500;

  (* Atom types *)
  IntValue  = 0;    (* 16 bytes *)
  LinkValue = 1;    (* 16 bytes *)
  FlatList  = 2;    (* 8 bytes + length of flat list *)


TYPE

  Address = SYSTEM.ADDRESS;
  AtomPtr = POINTER [1] TO Atom;
  Atom = RECORD
    next: Address;  (* Bottom bit of next determines use of value below *)
    data: Address   (* next MOD 2 = 0: integer value, 1: link address *)
  END;

  Value = RECORD
    type:   Address;  (* Either IntValue or LinkValue. *)
    data:   Address;
    (* The following fields are only used when type is LinkValue, they
       cache the linked atom. *)
    ltype:   Address;  (* Linked atom type *)
    ldata:   Address;  (* Linked atom data *)
    lnext:   Address;  (* Next loc, following atom or whole flatlist. *)
    (* llength is nonzero only when the link is to  FlatList. *)
    llength: Address;  (* Set for FlatLists, 0 otherwise. *)
    loffset: Address;  (* FlatList only - cur pos in FlatList *)
    lbytes:  Address;  (* FlatList only - Length of cur entry in bytes *)
  END;

  ValueStack = RECORD
    stack: ARRAY StackDepth OF Value;
    top:   INTEGER
  END;

VAR
  Abort:     BOOLEAN;
  LineCount: INTEGER;
  Memory:    ARRAY AtomCount OF Atom;
  Free:      AtomPtr;

  Program: Value;
  Boot:    Value;

  LocalStack:   ValueStack;
  ProgramStack: ValueStack;
  LoopStack:    ValueStack;

  (* Standard global variables *)
  Input:    Value;
  Pattern:  Value;
  Sequence: Value;

  IntrinsicVariable: ARRAY 26 OF AtomPtr;

  BootState:  INTEGER;
  BootNumber: INTEGER;
  BootStack:  ARRAY 10 OF AtomPtr;
  BootTop:    INTEGER;

(* ---------------------- Current match/execution state --------------------- *)


(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)              END ws;
PROCEDURE wc(c: CHAR);           BEGIN TextWriter.Char(c)                END wc;
PROCEDURE ^wl;                 (*BEGIN TextWriter.NewLine                END wl;*)
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

PROCEDURE wl;
BEGIN
  TextWriter.NewLine;  INC(LineCount);
  IF LineCount > MaxLines THEN LineCount := 0; Fail("LineCount exceeded.") END
END wl;


(* ---------------------------- Unicode output ---------------------------- *)

PROCEDURE wut(u: LONGINT; n: INTEGER);
BEGIN
  IF n > 1 THEN wut(u DIV 64, n-1) END;
  wc(CHR(u MOD 64 + 080H))
END wut;

PROCEDURE wu(u: LONGINT);  (* Write Unicode codepoint as UTF-8 *)
BEGIN
  IF    u = 10      THEN wl  (* LF *)
  ELSIF u < 32      THEN wc('^'); wx(u,1)
  ELSIF u < 000080H THEN wc(CHR(u))
  ELSIF u < 000800H THEN wc(CHR(u DIV 00040H + 0C0H));  wut(u, 1)
  ELSIF u < 010000H THEN wc(CHR(u DIV 01000H + 0E0H));  wut(u, 2)
  ELSIF u < 110000H THEN wc(CHR(u DIV 40000H + 0F0H));  wut(u, 3)
  ELSE Fail("Write unicode value > 10FFFFH.")
  END
END wu;


(* ----------------------------- Atom access ------------------------------ *)

PROCEDURE BoolVal(b: BOOLEAN): Address;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE SetValOffset(VAR val: Value; offset: Address);
VAR addr: Address; byte: SYSTEM.INT8;
BEGIN
  ws("SetValOffset, offset "); wi(offset); wl;
  Assert(val.type = LinkValue, "Cannot SetValOffset for value type.");
  Assert(val.llength > 0, "SetValOffset expected FlatList atom.");
  Assert(offset < val.llength, "SetValOffset expected offset within flat list.");

  val.loffset := offset;
  addr := val.data + SIZE(Atom) + offset;
  SYSTEM.GET(addr, byte);

  IF byte >= 0 THEN (* A single byte positive integer *)
    val.ltype := IntValue;
    val.ldata := byte;
    val.lbytes := 1
  ELSE

    (* First bte of muti-byte value *)
    IF byte DIV 64 MOD 2 = 0 THEN val.ltype := IntValue ELSE val.ltype := LinkValue END;

    val.ldata := byte * 4 DIV 4;  (* Sign extend 6 to 8 bits *)
    INC(addr);  SYSTEM.GET(addr, byte);

    (* Middle bytes of multi-byet value *)
    WHILE byte < 0 DO
      val.ldata := val.ldata * 128  +  byte MOD 128;
      INC(addr);  SYSTEM.GET(addr, byte)
    END;

    (* Last byte of multi-byte value *)
    val.ldata := val.ldata * 128  +  byte;

    IF val.ltype = LinkValue THEN  (* Links are stored as offsets from the FlatList. *)
      INC(val.ldata, SYSTEM.ADR(val.data))
    END;

    val.lbytes := addr+1 - offset
  END
END SetValOffset;

PROCEDURE InitIntValue(VAR val: Value; int: Address);
BEGIN
  val.type := IntValue;
  val.data := int
END InitIntValue;

PROCEDURE InitLinkValue(VAR val: Value; link: AtomPtr);
BEGIN
  val.type := LinkValue;
  val.data := SYSTEM.VAL(Address, link);
  Assert(val.data MOD 4 = 0, "Invalid AtomPtr passed to InitLinkValue.");
  IF link # NIL THEN
    val.ltype := link.next MOD 4;
    val.lnext := link.next - val.ltype;

    IF val.ltype < FlatList THEN
      (* Cache content of non-flat atom *)
      val.llength := 0;
      val.loffset := 0;
      val.lbytes  := 0;
      val.ldata   := link.data
    ELSE
      (* Cache value of first atom in flatlist referenced by link. *)
      val.llength := link.data;
      SetValOffset(val, 0)
    END
  END
END InitLinkValue;

PROCEDURE Truth(v: Value): BOOLEAN;
BEGIN RETURN v.data # 0 END Truth;

PROCEDURE IsValue(v: Value): BOOLEAN;
BEGIN RETURN v.type = IntValue END IsValue;

PROCEDURE Next(VAR v: Value);
BEGIN
  IF v.type = IntValue THEN
    InitLinkValue(v, NIL)
  ELSE
    IF (v.llength = 0) OR (v.loffset + v.lbytes >= v.llength) THEN
      InitLinkValue(v, SYSTEM.VAL(AtomPtr, v.lnext))
    ELSE
      SetValOffset(v, v.loffset + v.lbytes)
    END
  END
END Next;

PROCEDURE EndOfList(VAR v: Value): BOOLEAN;
BEGIN RETURN (v.type = LinkValue) & (v.data = 0)
END EndOfList;

PROCEDURE Fetch(VAR val: Value);
BEGIN
  Assert(val.type = LinkValue, "Fetch(Value) expected a LinkValue.");
  IF val.ltype = IntValue THEN InitIntValue(val, val.ldata)
  ELSE InitLinkValue(val, SYSTEM.VAL(AtomPtr, val.ldata)) END
END Fetch;

PROCEDURE CopyValue(source: Value; target: AtomPtr);
BEGIN
  (*ws("Copy atom. Source: "); wa(source); ws(", Target: "); wa(target); wsl(".");*)
  target.data := source.data;
  target.next := target.next  -  target.next MOD 4  +  source.type
END CopyValue;

PROCEDURE Unflatten(VAR val: Value);
BEGIN
  Assert(val.llength = 0, "Unflattening not yet implemented.")
END Unflatten;

PROCEDURE StoreValue(source: Value; VAR target: Value);
BEGIN
  Assert(target.type = LinkValue, "Target of Store must be a LinkValue.");
  Unflatten(target);
  Assert(target.llength = 0, "Cannot store into flat list.");
  CopyValue(source, SYSTEM.VAL(AtomPtr, target.data));
  InitLinkValue(target, SYSTEM.VAL(AtomPtr, target.data));
END StoreValue;

PROCEDURE SetNext(a, b: AtomPtr);
BEGIN a.next := SYSTEM.VAL(Address, b) + a.next MOD 4
END SetNext;

PROCEDURE SetInt(a: AtomPtr; b: Address);
BEGIN
  a.data := b;
  a.next := a.next - a.next MOD 4 + IntValue
END SetInt;

PROCEDURE SetLink(a, b: AtomPtr);
BEGIN
  a.data := SYSTEM.VAL(Address, b);
  a.next := a.next - a.next MOD 4 + LinkValue;
END SetLink;

PROCEDURE NewAtom(): AtomPtr;
VAR result: AtomPtr;
BEGIN
  Assert(Free # NIL, "Out of memory.");
  result := Free;  Free := SYSTEM.VAL(AtomPtr, Free.next);
  result.next := 0;  result.data := 0;
RETURN result END NewAtom;

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

PROCEDURE wvalue(v: Value);
VAR l: Value;
BEGIN
  IF v.type = IntValue THEN
    wc('`'); wu(v.data)
  ELSE
    WHILE v.data # 0 DO
      IF v.ltype = IntValue THEN wu(v.ldata)
      ELSE
        wc('[');
        InitLinkValue(l, SYSTEM.VAL(AtomPtr, v.ldata)); wvalue(l);
        wc(']')
      END;
      Next(v)
    END
  END
END wvalue;

PROCEDURE DebugOut(v: Value);
BEGIN
  IF v.type = IntValue THEN
    ws('int '); wi(v.data)
  ELSE
    ws("list "); wvalue(v)
  END
END DebugOut;

PROCEDURE DumpValue(val: Value);
BEGIN
  ws("DumpValue");
  ws(". type ");    wi(val.type);
  ws(", data ");    wx(val.data, 16);
  ws(", ltype ");   wi(val.ltype);
  ws(", ldata ");   wx(val.ldata, 16);
  ws(", loffset "); wi(val.loffset);
  ws(", lbytes ");  wi(val.lbytes);
  ws(", llength "); wi(val.llength);
  ws(", lnext ");   wx(val.lnext, 16); wl
END DumpValue;


(* -------------------------------- Stacks -------------------------------- *)

PROCEDURE PushValue(VAR stack: ValueStack; VAR val: Value);
BEGIN
  Assert(stack.top < LEN(stack.stack), "Stack overflow.");
  stack.stack[stack.top] := val;
  INC(stack.top)
END PushValue;

PROCEDURE PushInt(VAR stack: ValueStack; i: Address);
VAR v: Value;
BEGIN InitIntValue(v, i); PushValue(stack, v) END PushInt;

PROCEDURE PushAtomPtr(VAR stack: ValueStack; ptr: AtomPtr);
VAR val: Value;
BEGIN
  (*ws("PushAtomPtr atom at "); wx(SYSTEM.VAL(Address, ptr), 1); wl;*)
  InitLinkValue(val, ptr);
  (*
  ws("PushAtomPtr: InitLinkValue result: ");
  ws(", type ");    wi(val.type);
  ws(", data ");    wx(val.data, 16);
  ws(", ltype ");   wi(val.ltype);
  ws(", ldata ");   wx(val.ldata, 16);
  ws(", loffset "); wi(val.loffset);
  ws(", lbytes ");  wi(val.lbytes);
  ws(", llength "); wi(val.llength);
  ws(", lnext ");   wx(val.lnext, 16); wl;
  ws("PushAtomPtr: InitLinkValue result as value "); wvalue(val); wl;
  *)
  PushValue(stack, val)
END PushAtomPtr;

PROCEDURE PopValue(VAR stack: ValueStack; VAR val: Value);
BEGIN
  Assert(stack.top > 0, "Stack undeflow.");
  DEC(stack.top);
  val := stack.stack[stack.top]
END PopValue;

PROCEDURE Dup(VAR stack: ValueStack);
BEGIN
  Assert(stack.top > 0, "Cannot dup empty stack.");
  Assert(stack.top < LEN(stack.stack), "Cannot up full stack.");
  stack.stack[stack.top] := stack.stack[stack.top-1];
  INC(stack.top)
END Dup;

PROCEDURE Swap(VAR stack: ValueStack);
VAR val: Value;
BEGIN
  Assert(stack.top > 1, "Swap requires at least two items on stack.");
  val := stack.stack[stack.top-2];
  stack.stack[stack.top-2] := stack.stack[stack.top-1];
  stack.stack[stack.top-1] := val
END Swap;

PROCEDURE Drop(VAR stack: ValueStack);
BEGIN
  Assert(stack.top > 0, "Cannot drop from empty stack.");
  DEC(stack.top)
END Drop;

PROCEDURE DumpStack(VAR stack: ValueStack);
VAR i: INTEGER;
BEGIN
  (* Dump any remaining stack content *)
  IF stack.top = 0 THEN wsl("stack empty.")
  ELSE wsl("stack content:");
    i := stack.top-1;  WHILE i >= 0 DO
      ws("  ["); wi(i); ws("] "); wvalue(stack.stack[i]); wl;
      DEC(i)
    END
  END
END DumpStack;



(* ---------------------- Intrinsic variables (a..z) ---------------------- *)

(*
PROCEDURE MakeIntrinsicVariable(VAR a: AtomPtr; c: CHAR);
BEGIN
  a := NewAtom();  IntrinsicVariable[ORD(c) - ORD('a')] := a;
END MakeIntrinsicVariable;
*)


(* ---------------------------- Atom functions ---------------------------- *)


(* ----------------------------- Interpreter ------------------------------ *)

PROCEDURE Step;
VAR n, r1, r2: Value;  c: CHAR;  i: Address;
BEGIN
  Assert(~EndOfList(Program), "Program must not be at end of list at start of Step.");
  IF IsValue(Program) THEN  (* Hack *)
    Program.ldata := Program.data;  Program.ltype := IntValue
  END;
  n := Program;  Next(n);
  IF Program.ltype = IntValue THEN
    (*ws("Intrinsic '"); wu(Program.ldata); wsl("'.");*)
    CASE CHR(Program.ldata) OF
    |' ', 0AX, 0DX: (* No op   *)

    (* Intrinsic global variables a..z and integer literals 0..F *)
    |'a'..'z':         i := Program.ldata - ORD('a');
                       IF IntrinsicVariable[i] = NIL THEN IntrinsicVariable[i] := NewAtom() END;
                       PushAtomPtr(LocalStack, IntrinsicVariable[i]);
                       (*ws("Following initrinsic variable push, "); DumpStack(LocalStack); wl*)
    |'0'..'9':         PushInt(LocalStack, Program.ldata - ORD('0'))
    |'A'..'F':         PushInt(LocalStack, Program.ldata - ORD('A') + 10)
    |'`':              Assert(n.ltype = IntValue, "` expected value.");
                       PushInt(LocalStack, n.ldata);  Next(n)

    (* Stack manipulation *)
    |'"':(* Dup     *) Dup(LocalStack);
    |'%':(* Swap    *) Swap(LocalStack);
    |'#':(* Drop    *) Drop(LocalStack);

    (* Basic operations *)
    |'~':(* Not     *) PopValue(LocalStack, r1); PushInt(LocalStack, BoolVal(~Truth(r1)))
    |'=':(* Equal   *) PopValue(LocalStack, r2); PopValue(LocalStack, r1);
                       IF r1.type # r2.type THEN PushInt(LocalStack, 0)
                       ELSIF r1.type = IntValue THEN PushInt(LocalStack, BoolVal(r1.data=r2.data))
                       ELSE PushInt(LocalStack, BoolVal((r1.data=r2.data) & (r1.loffset = r2.loffset)))
                       END
    |'+':(* Plus    *) PopValue(LocalStack, r2); PopValue(LocalStack, r1);
                       Assert(r1.type = IntValue, "+ requires integer value parameters.");
                       Assert(r2.type = IntValue, "+ requires integer value parameters.");
                       PushInt(LocalStack, r1.data + r2.data)
    |'-':(* Minus   *) PopValue(LocalStack, r2); PopValue(LocalStack, r1);
                       Assert(r1.type = IntValue, "- requires integer value parameters.");
                       Assert(r2.type = IntValue, "- requires integer value parameters.");
                       PushInt(LocalStack, r1.data - r2.data)
    |'&':(* And     *) PopValue(LocalStack, r2); PopValue(LocalStack, r1);
                       PushInt(LocalStack, BoolVal(Truth(r1) & Truth(r2)));

    (* Conditional *)
    |'?':(* If      *) PopValue(LocalStack, r2); PopValue(LocalStack, r1);
                       (*wsl("'?':"); ws("TOS "); DumpValue(r2); ws("SOS "); DumpValue(r1);*)
                       IF Truth(r1) THEN
                         IF IsValue(r2) THEN
                           InitIntValue(n, r2.data)
                         ELSE
                           n := r2
                         END
                       END;

    (* Atom access *)
    |'_':(* is Link *) PopValue(LocalStack, r1); PushInt(LocalStack, BoolVal(r1.type = LinkValue))
    |',':(* Next    *) Assert(LocalStack.top > 0, "Next requires an item on the stack.");
                       Next(LocalStack.stack[LocalStack.top-1])
    |'.':(* Fetch   *) Assert(LocalStack.top > 0, "Fetch requires an item on the stack.");
                       Fetch(LocalStack.stack[LocalStack.top-1])
    |':':(* Store   *) PopValue(LocalStack, r2); PopValue(LocalStack, r1);
                       (*wsl("Store:"); ws("TOS "); DumpValue(r2); ws("SOS "); DumpValue(r1);*)
                       Assert(~IsValue(r2), "Store requies link at top of stack");
                       StoreValue(r1, r2);

    (* Control transfer *)
    |'!':(* Execute *) PushValue(ProgramStack, n);
                       PopValue(LocalStack, n);
                       PushValue(ProgramStack, n)
    |'@':(* Loop    *) n := ProgramStack.stack[ProgramStack.top-1]

    (* Input and output *)
    |'R':(* Input   *) In.Char(c);  PushInt(LocalStack, ORD(c))
    |'W':(* Output  *) PopValue(LocalStack, r1); wvalue(r1); wfl
    |'L':(* Newline *) wl
    |'S':(* DumpStk *) DumpStack(LocalStack)
    |'N':(* NIL     *) PushAtomPtr(LocalStack, NIL)
    |'X':(* DbgExit *) Fail("'X' intrinsic - Forced debug exit.")
    ELSE wlc; ws("Unrecognised intrinsic code: ");
      wi(Program.ldata); wc(' '); wu(Program.ldata); Fail("")
    END
  ELSE  (* handle program link - i.e.push linked list *)
    r1 := Program; Fetch(r1); PushValue(LocalStack, r1)
  END;
  Program := n;
  (* When Program = NIL we've reached end of function and must return to caller *)
  WHILE (EndOfList(Program)) & (ProgramStack.top > 0) DO
    (*ws("Droplevel because Program is "); wvalue(Program); wl;*)
    Drop(ProgramStack);  PopValue(ProgramStack, Program)
  END
END Step;



(* -------------------------------- Matching ------------------------------ *)

(*
PROCEDURE InitMatchList(pattern: AtomPtr);
BEGIN
  SetInt(Sequence, BoolVal(Value(pattern) = ORD("'")));
  Pattern := Next(pattern);
END InitMatchList;

PROCEDURE Backtrack(matched: BOOLEAN);
VAR prevInput: AtomPtr;
BEGIN
  IF Link(LocalStack) = NIL THEN  ( * Pattern is complete * )
    LocalStack := Next(LocalStack); PushValue(LocalStack, BoolVal(matched));
    Pattern := NIL
  ELSE
    Pattern := PopLink(LocalStack);
    IF matched THEN LocalStack := Next(LocalStack) ELSE SetLink(Input, PopLink(LocalStack)) END;
    Assert(IsValue(LocalStack), "Expected Saved Sequence value on local stack.");
    SetInt(Sequence, Value(LocalStack));  LocalStack := Next(LocalStack);
    IF matched = (Value(Sequence)#0) THEN
      Pattern := Next(Pattern)
    ELSE ( * Failure during sequence, or success of a choice * )
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
    IF ((Value(Sequence)#0) = equal) & (Next(Pattern) # NIL) THEN  ( * move to next in list * )
      Pattern := Next(Pattern)
    ELSE  ( * look no further in list * )
      Backtrack(equal)
    END
  ELSE
    PushValue(LocalStack, Value(Sequence));
    PushAtomPtr(LocalStack, Link(Input));
    PushAtomPtr(LocalStack, Pattern);
    InitMatchList(Link(Pattern))
  END;
END MatchStep;

PROCEDURE StartMatch(pattern: AtomPtr);
BEGIN
  PushAtomPtr(LocalStack, NIL);
  InitMatchList(pattern)
END StartMatch;
*)

(* ------------------------------- Bootstrap -------------------------------- *)

(* BootState:
     0 - normal
     1 - escaped
     2 - number
*)

PROCEDURE AddBootstrapAtom(VAR current: AtomPtr);
VAR next: AtomPtr;
BEGIN next := NewAtom();  SetNext(current, next);  current := next
END AddBootstrapAtom;

PROCEDURE BootstrapAddChar(VAR current: AtomPtr;  ch: CHAR);
VAR link: AtomPtr;
BEGIN
  IF (BootState = 2) & ((ch < '0') OR (ch > '9')) THEN
    AddBootstrapAtom(current);  SetInt(current, BootNumber);
    ws("Boot escaped number "); wi(BootNumber); wl;
    BootState := 0;
  END;
  CASE BootState OF
  |0: CASE ch OF
      |'^': BootState := 1;
      |'[': AddBootstrapAtom(current);  BootStack[BootTop] := current;  INC(BootTop);
      |']': (*
            ws("']' handler. current.next "); wx(current.next, 16);
            ws(", current.data "); wx(current.data, 16); wl;
            *)
            DEC(BootTop);  link := BootStack[BootTop];
            link.data := link.next - link.next MOD 4;
            link.next := LinkValue;
            Assert(current.next - current.next MOD 4 = 0, "Expected current.next to be at EOL in ']'.");
            current := link;
      ELSE  AddBootstrapAtom(current);  SetInt(current, ORD(ch))
      END
  |1: IF (ch >= '0') & (ch <= '9') THEN
        BootNumber := ORD(ch) - ORD('0');
        ws("Boot escaped number. First digit "); wi(BootNumber); wl;
        BootState := 2;
      ELSE
        AddBootstrapAtom(current);  SetInt(current, ORD(ch));
        BootState := 0
      END
  |2: BootNumber := BootNumber*10 + ORD(ch) - ORD('0')
  ELSE Fail("Invalid boot state.")
  END
END BootstrapAddChar;

PROCEDURE BootstrapLoader(s: ARRAY OF CHAR): AtomPtr;
VAR head, current: AtomPtr;  i: INTEGER;
BEGIN i := 0; BootTop := 0;
  head := NewAtom();  current := head;  BootState := 0;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO
    BootstrapAddChar(current, s[i]);  INC(i)
  END;
  current := SYSTEM.VAL(AtomPtr, head.next - head.next MOD 4);
RETURN current END BootstrapLoader;

PROCEDURE LoadBoostrap(): AtomPtr;
VAR head, current, nest: AtomPtr;
    i:                   INTEGER;
    f:                   Files.File;
    r:                   Files.Rider;
    c:                   CHAR;
BEGIN BootTop := 0;
  head := NewAtom();  current := head;  BootState := 0;
  f := Files.Old("dam.boot");  Assert(f # NIL, "Expected file dam.boot.");
  Files.Set(r, f, 0);  Files.Read(r, c);
  WHILE ~r.eof DO
    IF c # 0DX THEN BootstrapAddChar(current, c) END;
    Files.Read(r, c)
  END;
  current := SYSTEM.VAL(AtomPtr, head.next - head.next MOD 4);
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
  InitLinkValue(Program, BootstrapLoader(s));
  WHILE ~EndOfList(Program) DO Step END;
END TestIntrinsicCode;

(*
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
*)

(* ------------------ Garbage collection experimentiation ----------------- *)

(*
PROCEDURE Used(a: AtomPtr);
TYPE
  AtomAsSetsPtr = POINTER TO AtomAsSets;
  AtomAsSets = RECORD next, data: SET END;
VAR sp: AtomAsSetsPtr;
BEGIN
  IF (a # NIL) & ((a.next MOD 4) < 2) THEN  ( * If not already marked used * )
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


PROCEDURE MarkClass(a: AtomPtr; c: CHAR; VAR class: ARRAY OF CHAR);
BEGIN
  WHILE a # NIL DO
    class[(SYSTEM.VAL(Address, a) - SYSTEM.ADR(Memory[0])) DIV SIZE(Atom)] := c;
    IF ~IsValue(a) THEN MarkClass(Link(a), c, class) END;
    a := Next(a)
  END
END MarkClass;

PROCEDURE DisplayUsed;
CONST rowlength = 100;
TYPE
  AtomAsSetsPtr = POINTER TO AtomAsSets;
  AtomAsSets = RECORD next, data: SET END;
VAR sp: AtomAsSetsPtr;  i: INTEGER;  class: ARRAY AtomCount OF CHAR; a: AtomPtr;
BEGIN
  FOR i := 0 TO LEN(Memory)-1 DO
    sp := SYSTEM.VAL(AtomAsSetsPtr, SYSTEM.ADR(Memory[i]));
    IF 1 IN sp^.next THEN class[i] := "U" ELSE class[i] := "." END;
  END;

  MarkClass(Free, 'F', class);

  FOR i := ORD('a') TO ORD('z') DO
    MarkClass(IntrinsicVariable[i - ORD('a')], CHR(i), class)
  END;

  MarkClass(Program, 'P', class);
  MarkClass(ProgramStack, 'p', class);
  MarkClass(LocalStack, 'l', class);

  ws("  ");
  i := 0; WHILE i < AtomCount DO
    wc(class[i]);
    INC(i);
    IF i MOD rowlength = 0 THEN wl; ws("  ") END
  END;
  IF i MOD rowlength # 0  THEN wl END;
END DisplayUsed;

PROCEDURE Garbage;
TYPE
  AtomAsSetsPtr = POINTER TO AtomAsSets;
  AtomAsSets = RECORD next, data: SET END;
VAR i: INTEGER; sp: AtomAsSetsPtr;
BEGIN
  wl; wsl("Garbage experiments.");
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

  CountUsed;  ( * DisplayUsed * )
END Garbage;
*)

(* ----------------------------- Startup code ----------------------------- *)

BEGIN
  LineCount := 0;
  Assert(SYSTEM.VAL(Address, NIL) = 0, "Expected NIL to be zero.");
  ws("Address size is "); wi(SIZE(Address)*8); wsl(" bits.");
  InitMemory;
  Free := SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory));
  (*TestNewAtom;*)

  (*
  MakeIntrinsicVariable(Input,    'i');
  MakeIntrinsicVariable(Pattern,  'p');
  MakeIntrinsicVariable(Sequence, 's');
  *)

  (*
  TestOberonCodedMatching;
  *)

  InitLinkValue(Boot, LoadBoostrap());  (*DumpList(Boot);*)
  (* Run the bootstrap *)
  Program := Boot;  WHILE ~EndOfList(Program) DO Step END;


  wl; ws("Bootstrap complete, "); DumpStack(LocalStack);

  (* Garbage detection *)
  (*
  Garbage
  *)

END dam.

