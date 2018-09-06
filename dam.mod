MODULE dam;  (* dam - data, algorithms and memory *)

IMPORT Strings, Files, TextWriter, SYSTEM, In;

CONST
  BlockCount = 6000;
  StackDepth = 100;
  MaxBuffer  = 1024;
  MaxLines   = 500;

  (* Kinds *)
  Int  = 0;
  Link = 1;
  Flat = 2;

TYPE

  Address = SYSTEM.ADDRESS;
  Byte    = SYSTEM.INT8;

  BlockHeader = RECORD
    next: Address;  (* MOD 4 -> Int (0), Link (1) or FLat (2). *)
    data: Address;  (* Integer value, link address or flatlist limit. *)
    (* Flat list content immediately follows the header and continues
       to the limit stored in .data. *)
  END;
  BlockPtr* = POINTER [1] TO BlockHeader;

  Value* = RECORD
    header-:  BlockPtr; (* Address of current BlockHeader, NIL if refkind is int. *)
    kind-:    Address;  (* Int or Link *)
    data-:    Address;  (* Integer value or adress of BlockHeader *)
    (* Private cache for link into flatlist, 0 if not flat *)
    flatnext: Address;  (* Offset of next value, 0 if none, or not flat *)
  END;

  ValueStack = RECORD
    stk: ARRAY StackDepth OF Value;
    top: INTEGER
  END;

VAR
  LineCount: INTEGER;
  Memory:    ARRAY BlockCount OF BlockHeader;
  Free:      BlockPtr;

  Program: Value;
  Boot:    Value;

  Arg:    ValueStack;
  Return: ValueStack;
  Loop:   ValueStack;

  IntrinsicVariable: ARRAY 26 OF Address;

  BootState:  INTEGER;
  BootNumber: INTEGER;
  BootStack:  ARRAY 10 OF BlockPtr;
  BootTop:    INTEGER;

  FlatListBuffer: ARRAY MaxBuffer OF Byte;
  FlatListOffset: Address;

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

(* ---------------------------- FLattened values ---------------------------- *)

PROCEDURE- BitwiseAnd(a,b: LONGINT): LONGINT "((a) & (b))";

PROCEDURE CompressValue(kind, data: Address; VAR buf: ARRAY OF Byte; VAR offset: Address);
VAR val: ARRAY 10 OF Byte; i: INTEGER;
BEGIN
  Assert(kind < 2, "CompressValue expected Int or Link type.");
  IF (kind = Int) & (data >= 0) & (data < 128) THEN
    (* The compressed values is just the data itself *)
    buf[offset] := SYSTEM.VAL(Byte, data);  INC(offset)
  ELSE
    i := 0;
    REPEAT
      val[i] := SYSTEM.VAL(Byte, data MOD 128);
      data := data DIV 128;  (* Note, sign extends *)
      INC(i)
    UNTIL (i >= 10) OR (((data = -1) OR (data = 0)) & (i > 1));

    IF BitwiseAnd(val[i-1], 60H) # BitwiseAnd(data, 60H) THEN
      val[i] := SYSTEM.VAL(Byte, data); INC(i)
    END;

    DEC(i);
    buf[offset] := val[i] MOD 64 + SYSTEM.VAL(Byte, kind*64) + 127+1;
    INC(offset); DEC(i);
    WHILE i > 0 DO buf[offset] := val[i]+127+1; INC(offset); DEC(i) END;
    buf[offset] := val[0]; INC(offset)
  END
END CompressValue;

PROCEDURE ExpandValue(addr: Address; VAR v: Value);
VAR byte: Byte;
BEGIN
  SYSTEM.GET(addr, byte);
  IF byte >= 0 THEN
    v.kind := Int; v.data := byte
  ELSE
    v.kind := byte DIV 64 MOD 2;
    (* First byte of muti-byte value *)
    byte := byte * 4;  (* Sign extend 6 to 8 bits *)
    v.data := byte DIV 4;
    INC(addr);
    SYSTEM.GET(addr, byte);
    (* Middle bytes of multi-byte value *)
    WHILE byte < 0 DO
      v.data := v.data * 128  +  byte MOD 128;
      INC(addr);
      SYSTEM.GET(addr, byte)
    END;
    (* Last byte of multi-byte value *)
    v.data := v.data * 128 + byte
  END;
  INC(addr);
  Assert(addr <= v.header.data, "Decoded flat value extended past end of flat block.");
  IF addr < v.header.data THEN v.flatnext := addr ELSE v.flatnext := 0 END
END ExpandValue;



(* --------------------------------- Values --------------------------------- *)

PROCEDURE InitInt(VAR v: Value; i: Address);
BEGIN
  v.header   := NIL;
  v.kind     := Int;
  v.data     := i;
  v.flatnext := 0;
END InitInt;

PROCEDURE InitLink(VAR v: Value; blockheader: Address);
BEGIN
  Assert(blockheader MOD 4 = 0, "InitBlockRefernce expects address with bits 0 and 1 = 0.");
  Assert(blockheader # 0, "Cannot InitLink from NIL.");
  v.header := SYSTEM.VAL(BlockPtr, blockheader);
  v.kind   := v.header.next MOD 4;
  IF v.kind < Flat THEN
    v.data     := v.header.data;
    v.flatnext := 0
  ELSE  (* Set up for link into flat list *)
    ExpandValue(blockheader + SIZE(BlockHeader), v)
  END
END InitLink;

PROCEDURE IsLink(VAR v: Value): BOOLEAN;
BEGIN RETURN v.header # NIL END IsLink;

PROCEDURE Truth*(VAR v: Value): BOOLEAN;
BEGIN RETURN IsLink(v) OR (v.data # 0) END Truth;

PROCEDURE Fetch*(VAR v: Value);
BEGIN
  Assert(IsLink(v), "Fetch expects reference that is a Link, not an Int.");
  IF v.kind = Int THEN InitInt(v, v.data)
  ELSE InitLink(v, v.data) END
END Fetch;

PROCEDURE Next*(VAR v: Value);
BEGIN
  Assert(IsLink(v), "Next expects reference that is a Link, not an Int.");
  IF v.flatnext # 0 THEN  ExpandValue(v.flatnext, v)
  ELSIF v.header.next DIV 4 = 0 THEN InitInt(v, 0)
  ELSE InitLink(v, v.header.next - v.header.next MOD 4)
  END
END Next;

PROCEDURE StoreValue(source: Value; VAR target: Value);
VAR a: BlockPtr;
BEGIN
  Assert(IsLink(target), "Target reference of Store must be a link.");
  IF target.header.next MOD 4 = Flat THEN
    Fail("Unflattening not yet implemented.")
  END;
  IF ~IsLink(source) THEN
    target.header.next := target.header.next - target.header.next MOD 4 + Int;
    target.header.data := source.data
  ELSE
    target.header.next := target.header.next - target.header.next MOD 4 + Link;
    target.header.data := SYSTEM.VAL(Address, source.header)
  END;
  InitLink(target, SYSTEM.VAL(Address, target.header))
END StoreValue;


(* --------------------------------- Blocks --------------------------------- *)

PROCEDURE NewBlock(): BlockPtr;
VAR result: BlockPtr;
BEGIN
  Assert(Free # NIL, "Out of memory.");
  result := Free;  Free := SYSTEM.VAL(BlockPtr, Free.next);
  result.next := 0;  result.data := 0;
RETURN result END NewBlock;

PROCEDURE InitMemory;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO LEN(Memory)-2 DO
    Memory[i].next := SYSTEM.ADR(Memory[i+1]);
    Memory[i].data := 0;
  END;
  Memory[LEN(Memory)-1].next := 0;
  Memory[LEN(Memory)-1].data := 0;
  FOR i := 0 TO LEN(IntrinsicVariable)-1 DO IntrinsicVariable[i] := 0 END;
  Free := SYSTEM.VAL(BlockPtr, SYSTEM.ADR(Memory))
END InitMemory;


(* ----------------------------- Test harness ----------------------------- *)

PROCEDURE wvalue(v: Value);
VAR l: Value;
BEGIN
  IF ~IsLink(v) THEN
    wu(v.data)
  ELSE
    WHILE IsLink(v) DO
      IF v.kind = Int THEN wu(v.data)
      ELSE wc('['); l := v; Fetch(l); wvalue(l); wc(']') END;
      Next(v)
    END
  END
END wvalue;

PROCEDURE DumpReference(v: Value);
BEGIN
  ws("DumpReference");
  ws(". Header ");   wx(SYSTEM.VAL(Address, v.header), 16);
  ws(", kind ");     IF    v.kind = Int  THEN ws("Int")
                     ELSIF v.kind = Link THEN ws("Link")
                     ELSE ws("invalid "); wi(v.kind) END;
  ws(", data ");     wx(v.data, 16);
  ws(", flatnext "); wx(v.flatnext, 16); wl
END DumpReference;


(* -------------------------------- Stacks -------------------------------- *)

PROCEDURE Dup(VAR stk: ValueStack);
BEGIN
  Assert(stk.top > 0, "Cannot dup empty stk.");
  Assert(stk.top < LEN(stk.stk), "Cannot up full stk.");
  stk.stk[stk.top] := stk.stk[stk.top-1];
  INC(stk.top)
END Dup;

PROCEDURE Swap(VAR stk: ValueStack);
VAR v: Value;
BEGIN
  Assert(stk.top > 1, "Swap requires at least two items on stk.");
  v := stk.stk[stk.top-2];
  stk.stk[stk.top-2] := stk.stk[stk.top-1];
  stk.stk[stk.top-1] := v
END Swap;

PROCEDURE Drop(VAR stk: ValueStack);
BEGIN
  Assert(stk.top > 0, "Cannot drop from empty stk.");
  DEC(stk.top)
END Drop;

PROCEDURE DumpStack(VAR stk: ValueStack);
VAR i: INTEGER;
BEGIN
  (* Dump any remaining stk content *)
  IF stk.top = 0 THEN wsl("stack empty.")
  ELSE wsl("stk content:");
    FOR i := 0 TO stk.top-1 DO
      ws("  ["); wi(i); ws("] ");
      wvalue(stk.stk[stk.top-1-i]); wl;
    END
  END
END DumpStack;


(* ----------------------------- Interpreter ------------------------------ *)

PROCEDURE BoolVal(b: BOOLEAN): Address;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE Step;
VAR n, r1, r2: Value;  c: CHAR;  i: Address;
BEGIN
  Assert(IsLink(Program), "Step expects Program to be a link.");
  n := Program; Next(n);
  IF Program.kind = Int THEN
    (*ws("Intrinsic '"); wu(Program.data); wsl("'.");*)
    CASE CHR(Program.data) OF
    |' ', 0AX, 0DX: (* No op   *)

    (* Intrinsic global variables a..z and integer literals 0..F *)
    |'a'..'z':         Assert(Arg.top < StackDepth, "intrinsic variable blocked because arg stack is full.");
                       i := Program.data - ORD('a');
                       IF IntrinsicVariable[i] = 0 THEN
                         IntrinsicVariable[i] := SYSTEM.VAL(Address, NewBlock())
                       END;
                       InitLink(Arg.stk[Arg.top], IntrinsicVariable[i]); INC(Arg.top)
                       (*ws("Following initrinsic variable push, "); DumpStack(Arg); wl*)

    |'0'..'9':         Assert(Arg.top < StackDepth, "Intrinsic literal blocked because arg stack is full.");
                       INC(Arg.top); InitInt(Arg.stk[Arg.top-1], Program.data - ORD('0'))

    |'A'..'F':         Assert(Arg.top < StackDepth, "Intrinsic literal blocked because arg stack is full.");
                       INC(Arg.top); InitInt(Arg.stk[Arg.top-1], Program.data - ORD('A') + 10)

    |'`':              Assert(Arg.top < StackDepth, "'`' literal blocked because arg stack is full.");
                       Assert(n.kind = Int, "'`' expected Int.");
                       INC(Arg.top); InitInt(Arg.stk[Arg.top-1], n.data);
                       Next(n)

    (* Stack manipulation *)
    |'"':(* Dup     *) Dup(Arg);
    |'%':(* Swap    *) Swap(Arg);
    |'#':(* Drop    *) Drop(Arg);

    (* Basic operations *)
    |'~':(* Not     *) Assert(Arg.top >= 1, "'~' operator requires 1 arg.");
                       InitInt(Arg.stk[Arg.top-1], BoolVal(~Truth(Arg.stk[Arg.top-1])))

    |'=':(* Equal   *) Assert(Arg.top >= 2, "'=' operator requires 2 args.");
                       IF IsLink(Arg.stk[Arg.top-1]) # IsLink(Arg.stk[Arg.top-2]) THEN
                         InitInt(Arg.stk[Arg.top-2], 0)
                       ELSIF IsLink(Arg.stk[Arg.top-1]) THEN
                         InitInt(Arg.stk[Arg.top-2], BoolVal(Arg.stk[Arg.top-1].header = Arg.stk[Arg.top-2].header))
                       ELSE
                         InitInt(Arg.stk[Arg.top-2], BoolVal(Arg.stk[Arg.top-1].data = Arg.stk[Arg.top-2].data))
                       END;
                       DEC(Arg.top)

    |'+':(* Plus    *) Assert(Arg.top >= 2, "'+' operator requires 2 args.");
                       Assert(~IsLink(Arg.stk[Arg.top-1]), "'+' requires 2nd arg to be integer.");
                       Assert(~IsLink(Arg.stk[Arg.top-2]), "'+' requires 1st arg to be integer.");
                       InitInt(Arg.stk[Arg.top-2], Arg.stk[Arg.top-2].data + Arg.stk[Arg.top-1].data);
                       DEC(Arg.top)

    |'-':(* Minus   *) Assert(Arg.top >= 2, "'-' operator requires 2 args.");
                       Assert(~IsLink(Arg.stk[Arg.top-1]), "'-' requires 2nd arg to be integer.");
                       Assert(~IsLink(Arg.stk[Arg.top-2]), "'-' requires 1st arg to be integer.");
                       InitInt(Arg.stk[Arg.top-2], Arg.stk[Arg.top-2].data - Arg.stk[Arg.top-1].data);
                       DEC(Arg.top)

    |'&':(* And     *) Assert(Arg.top >= 2, "'&' operator requires 2 args.");
                       InitInt(Arg.stk[Arg.top-2], BoolVal(Truth(Arg.stk[Arg.top-2]) & Truth(Arg.stk[Arg.top-1])));
                       DEC(Arg.top)

    (* Conditional *)
    |'?':(* If      *) Assert(Arg.top >= 2, "'?' operator requires 2 args.");
                       Assert(IsLink(Arg.stk[Arg.top-1]), "'?' requires link on TOS.");
                       IF Truth(Arg.stk[Arg.top-2]) THEN n := Arg.stk[Arg.top-1] END;
                       DEC(Arg.top, 2)

    |'@':(* Start   *) Assert(Arg.top < StackDepth, "'@' blocked because arg stack is full.");
                       Assert(Return.top > 0, "'@' reqires at least one entry on return stack.");
                       INC(Arg.top);
                       Arg.stk[Arg.top-1] := Return.stk[Return.top-1]

    (* Block access *)
    |'_':(* IsLink  *) Assert(Arg.top >= 1, "'_' operator requires 1 arg.");
                       InitInt(Arg.stk[Arg.top-1], BoolVal(IsLink(Arg.stk[Arg.top-1])))

    |',':(* Next    *) Assert(Arg.top > 0, "Next requires an item on the stk.");
                       Next(Arg.stk[Arg.top-1])

    |'.':(* Fetch   *) Assert(Arg.top > 0, "Fetch requires an item on the stk.");
                       Fetch(Arg.stk[Arg.top-1])

    |':':(* Store   *) Assert(Arg.top >= 2, "':' store operator requires 2 args.");
                       Assert(IsLink(Arg.stk[Arg.top-1]), "Store requires link at top of stack.");
                       StoreValue(Arg.stk[Arg.top-2], Arg.stk[Arg.top-1]);
                       DEC(Arg.top, 2);

    (* Control transfer *)
    |'!':(* Execute *) Assert(Return.top < StackDepth-1, "Cannot enter nested list as return stack is full.");
                       Assert(Arg.top >= 1, "'!' execute operator requires 1 arg.");
                       INC(Return.top); Return.stk[Return.top-1] := n;
                       n := Arg.stk[Arg.top-1];  DEC(Arg.top);
                       Assert(IsLink(n), "'!' execute expects Link.");
                       INC(Return.top); Return.stk[Return.top-1] := n;

    (* Input and output *)
    |'R':(* Input   *) Assert(Arg.top < StackDepth, "'R' read blocked because arg stack is full.");
                       In.Char(c);  INC(Arg.top);  InitInt(Arg.stk[Arg.top-1], ORD(c))

    |'W':(* Output  *) Assert(Arg.top >= 1, "W operator requires 1 arg.");
                       wvalue(Arg.stk[Arg.top-1]); DEC(Arg.top); wfl

    |'L':(* Newline *) wl

    |'S':(* DumpStk *) DumpStack(Arg)

    |'X':(* DbgExit *) Fail("'X' intrinsic - Forced debug exit.")

    ELSE wlc; ws("Unrecognised intrinsic code: ");
      wi(Program.data); wc(' '); wu(Program.data); Fail("")
    END
  ELSE  (* handle program link - i.e.push linked list *)
    Assert(Arg.top < StackDepth, "Push link blocked because arg stack is full.");
    Fetch(Program);  INC(Arg.top);  Arg.stk[Arg.top-1] := Program
  END;
  Program := n;
  (* When Program is not a link we've reached end of function and must return to caller *)
  WHILE (~IsLink(Program)) & (Return.top > 1) DO
    DEC(Return.top);  Program := Return.stk[Return.top-1];  DEC(Return.top);
  END
END Step;


(* ------------------------------- Bootstrap -------------------------------- *)

(* BootState:
     0 - normal
     1 - escaped
     2 - number
*)

PROCEDURE AddBootstrapBlock(VAR current: BlockPtr; data: Address);
BEGIN
  current.next := SYSTEM.VAL(Address, NewBlock()) + current.next MOD 4;
  current := SYSTEM.VAL(BlockPtr, current.next - current.next MOD 4);
  current.data := data
END AddBootstrapBlock;

PROCEDURE BootstrapAddChar(VAR current: BlockPtr;  ch: CHAR);
VAR link: BlockPtr;
BEGIN
  IF (BootState = 2) & ((ch < '0') OR (ch > '9')) THEN
    AddBootstrapBlock(current, BootNumber);
    ws("Boot escaped number "); wi(BootNumber); wl;
    BootState := 0;
  END;
  CASE BootState OF
  |0: CASE ch OF
      |'^': BootState := 1;
      |'[': AddBootstrapBlock(current, 0);  BootStack[BootTop] := current;  INC(BootTop);
      |']': DEC(BootTop);  link := BootStack[BootTop];
            link.data := link.next - link.next MOD 4;
            link.next := Link;
            Assert(current.next - current.next MOD 4 = 0, "Expected current.next to be at EOL in ']'.");
            current := link;
      ELSE  AddBootstrapBlock(current, ORD(ch))
      END
  |1: IF (ch >= '0') & (ch <= '9') THEN
        BootNumber := ORD(ch) - ORD('0');
        ws("Boot escaped number. First digit "); wi(BootNumber); wl;
        BootState := 2;
      ELSE
        AddBootstrapBlock(current, ORD(ch));
        BootState := 0
      END
  |2: BootNumber := BootNumber*10 + ORD(ch) - ORD('0')
  ELSE Fail("Invalid boot state.")
  END
END BootstrapAddChar;

PROCEDURE LoadBoostrap(): BlockPtr;
VAR head, current, nest: BlockPtr;
    i:                   INTEGER;
    f:                   Files.File;
    r:                   Files.Rider;
    c:                   CHAR;
BEGIN BootTop := 0;
  head := NewBlock();  current := head;  BootState := 0;
  f := Files.Old("dam.boot");  Assert(f # NIL, "Expected file dam.boot.");
  Files.Set(r, f, 0);  Files.Read(r, c);
  WHILE ~r.eof DO
    IF c # 0DX THEN BootstrapAddChar(current, c) END;
    Files.Read(r, c)
  END;
  current := SYSTEM.VAL(BlockPtr, head.next - head.next MOD 4);
RETURN current END LoadBoostrap;


(* ------------------ Garbage collection experimentiation ----------------- *)

PROCEDURE ClearGarbageFlags;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO BlockCount-1 DO
    Memory[i].next := Memory[i].next - Memory[i].next MOD 16 + Memory[i].next MOD 4
  END
END ClearGarbageFlags;

PROCEDURE GetGarbageRefCount(b: BlockPtr): Address;
BEGIN RETURN b.next DIV 4 MOD 4 END GetGarbageRefCount;

PROCEDURE SetGarbageCount(b: BlockPtr; n: Address);
BEGIN
  b.next := b.next
          - b.next MOD 16
          + n * 4
          + b.next MOD 4;
END SetGarbageCount;

PROCEDURE GetNext(b: BlockPtr): BlockPtr;
BEGIN RETURN SYSTEM.VAL(BlockPtr, b.next - b.next MOD 16) END GetNext;

PROCEDURE AddGarbageCount(b: BlockPtr; n: INTEGER);
VAR count: Address; uncounted: BOOLEAN; link: BlockPtr;
BEGIN
  uncounted := TRUE;
  WHILE (b # NIL) & uncounted DO
    count := GetGarbageRefCount(b);
    uncounted := count = 0;
    INC(count, n); n := 1;
    IF count > 2 THEN count := 2 END;
    (*ws("SetGarbageCount "); wx(SYSTEM.VAL(Address, b), 16); ws(" to "); wi(count); wl;*)
    SetGarbageCount(b, count);
    IF uncounted & (b.next MOD 4 = Link) THEN
      AddGarbageCount(SYSTEM.VAL(BlockPtr, b.data), 2)
    END;
    b := GetNext(b)
  END
END AddGarbageCount;

PROCEDURE SetFreeToThree;
VAR b: BlockPtr;
BEGIN b := Free;
  WHILE b # NIL DO
    Assert(GetGarbageRefCount(b) = 0, "Expected free block to have 0 garbage count.");
    SetGarbageCount(b, 3);
    b := GetNext(b)
  END
END SetFreeToThree;

PROCEDURE MarkGarbageBlock(b: Value);
BEGIN
  Assert(IsLink(b), "MarkGarbageBlock expected value to be a link.");
  AddGarbageCount(b.header, 2)
END MarkGarbageBlock;

PROCEDURE MarkGarbage;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO Return.top - 1 DO MarkGarbageBlock(Return.stk[i]) END;
  FOR i := 0 TO Arg.top - 1 DO MarkGarbageBlock(Arg.stk[i]) END;
  FOR i := 0 TO Loop.top - 1 DO MarkGarbageBlock(Loop.stk[i]) END;
  MarkGarbageBlock(Boot);
  SetFreeToThree
END MarkGarbage;

PROCEDURE ShowGarbage;
CONST rowlength = 100;
VAR i: INTEGER;
BEGIN
  i := 0; WHILE i < BlockCount DO
    IF i MOD rowlength = 0 THEN ws("  ") END;
    wc(CHR(Memory[i].next DIV 4 MOD 4 + ORD('0')));
    INC(i);
    IF i MOD rowlength = 0 THEN wl END
  END;
  IF i MOD rowlength # 0  THEN wl END;
END ShowGarbage;

PROCEDURE GetPotentiallyFlatCount(block: BlockPtr): Address;
VAR count: Address;
BEGIN count := 0;
  WHILE (block # NIL) & (GetGarbageRefCount(block) = 1) DO
    INC(count);  block := GetNext(block)
  END;
RETURN count END GetPotentiallyFlatCount;

PROCEDURE whexbytes(VAR buf: ARRAY OF Byte; len: Address);
VAR i: Address;
BEGIN
  FOR i := 0 TO len-1 DO
    wx(buf[i],2);
    IF i < len-1 THEN wc(" ") END
  END
END whexbytes;

PROCEDURE Flatten(block: BlockPtr): BlockPtr;
VAR v: Value; buf: ARRAY MaxBuffer OF Byte; i: INTEGER;
BEGIN
  InitLink(v, SYSTEM.VAL(Address, block));
  i := 0;
  WHILE IsLink(v) & (GetGarbageRefCount(v.header) = 1) DO
    CompressValue(v.kind, v.data, FlatListBuffer, FlatListOffset);
    Next(v)
  END;
RETURN v.header END Flatten;

PROCEDURE MoveContigousToBufferSpace(block: BlockPtr);
VAR next: BlockPtr; count: Address;
BEGIN
  WHILE block # NIL DO
    next := GetNext(block);
    IF (next # NIL) & (GetPotentiallyFlatCount(next) > 2) THEN
      block.next := SYSTEM.VAL(Address, Flatten(next)) + block.next MOD 4;
      next := NIL  (* Prototype only collects one block *)
    END;
    block := next
  END
END MoveContigousToBufferSpace;

PROCEDURE TestMakeFlatValue(t, a: Address; verbose: BOOLEAN);
VAR buf: ARRAY 10 OF Byte; i, offset: Address; v: Value;
  dummy: BlockHeader;
BEGIN
  offset := 0;
  IF verbose THEN wx(a,16) END;
  CompressValue(t, a, buf, offset);
  IF verbose THEN ws(" flattened: "); whexbytes(buf, offset) END;

  v.header := SYSTEM.VAL(BlockPtr, SYSTEM.ADR(dummy));
  dummy.data := SYSTEM.ADR(buf) + offset;
  ExpandValue(SYSTEM.ADR(buf), v);

  IF verbose THEN
    ws(", decoded: type "); wx(v.kind,1); ws(" data "); wx(v.data,16); wl
  END;
  Assert(t=v.kind, "Flat value type lost.");
  Assert(a=v.data, "Flat value data lost.");
  Assert(v.flatnext = 0, "More bytes encoed than decoded.");
END TestMakeFlatValue;

PROCEDURE TestFlattening;
VAR a: Address;
BEGIN
  TestMakeFlatValue(0, 0,     TRUE);
  TestMakeFlatValue(0, 1,     TRUE);
  TestMakeFlatValue(0, 2,     TRUE);
  TestMakeFlatValue(0, 127,   TRUE);
  TestMakeFlatValue(0, 128,   TRUE);
  TestMakeFlatValue(0, 2047,  TRUE);
  TestMakeFlatValue(0, 2048,  TRUE);
  TestMakeFlatValue(0, 4095,  TRUE);
  TestMakeFlatValue(0, 4096,  TRUE);
  TestMakeFlatValue(0, -1,    TRUE);
  TestMakeFlatValue(0, -2,    TRUE);
  TestMakeFlatValue(0, -127,  TRUE);
  TestMakeFlatValue(0, -128,  TRUE);
  TestMakeFlatValue(0, -2048, TRUE);
  TestMakeFlatValue(0, -2049, TRUE);
  TestMakeFlatValue(0, -4096, TRUE);
  TestMakeFlatValue(0, -4097, TRUE);
  TestMakeFlatValue(1, 0,     TRUE);
  TestMakeFlatValue(1, 1,     TRUE);
  TestMakeFlatValue(1, 2,     TRUE);
  TestMakeFlatValue(1, 127,   TRUE);

  FOR a := 0 TO 5000000 DO TestMakeFlatValue(0, a, FALSE) END;
  FOR a := 0 TO 5000000 DO TestMakeFlatValue(0, -a, FALSE) END;

END TestFlattening;
(*

PROCEDURE CountUsed;
TYPE
  BlockAsSetsPtr = POINTER TO BlockAsSets;
  BlockAsSets = RECORD next, data: SET END;
VAR sp: BlockAsSetsPtr;  i, used, unused, free: INTEGER;  a: BlockPtr;
BEGIN
  used := 0;  free := 0;
  FOR i := 0 TO LEN(Memory)-1 DO
    sp := SYSTEM.VAL(BlockAsSetsPtr, SYSTEM.ADR(Memory[i]));
    IF 1 IN sp^.next THEN INC(used) ELSE INC(unused) END
  END;

  a := Free;  free := 0;
  WHILE a # NIL DO
    sp := SYSTEM.VAL(BlockAsSetsPtr, a);
    Assert(~(1 IN sp.next), "Expected all free list entries to be unused.");
    INC(free); a := Next(a)
  END;

  ws("Used "); wi(used); ws(", unused "); wi(unused);
  ws(", freelist "); wi(free); ws(", collectable "); wi(unused-free);
  wsl(".")
END CountUsed;


PROCEDURE MarkClass(a: BlockPtr; c: CHAR; VAR class: ARRAY OF CHAR);
BEGIN
  WHILE a # NIL DO
    class[(SYSTEM.VAL(Address, a) - SYSTEM.ADR(Memory[0])) DIV SIZE(Block)] := c;
    IF ~IsInt(a) THEN MarkClass(Link(a), c, class) END;
    a := Next(a)
  END
END MarkClass;

PROCEDURE DisplayUsed;
CONST rowlength = 100;
TYPE
  BlockAsSetsPtr = POINTER TO BlockAsSets;
  BlockAsSets = RECORD next, data: SET END;
VAR sp: BlockAsSetsPtr;  i: INTEGER;  class: ARRAY BlockCount OF CHAR; a: BlockPtr;
BEGIN
  FOR i := 0 TO LEN(Memory)-1 DO
    sp := SYSTEM.VAL(BlockAsSetsPtr, SYSTEM.ADR(Memory[i]));
    IF 1 IN sp^.next THEN class[i] := "U" ELSE class[i] := "." END;
  END;

  MarkClass(Free, 'F', class);

  FOR i := ORD('a') TO ORD('z') DO
    MarkClass(IntrinsicVariable[i - ORD('a')], CHR(i), class)
  END;

  MarkClass(Program, 'P', class);
  MarkClass(Return, 'p', class);
  MarkClass(Arg, 'l', class);

  ws("  ");
  i := 0; WHILE i < BlockCount DO
    wc(class[i]);
    INC(i);
    IF i MOD rowlength = 0 THEN wl; ws("  ") END
  END;
  IF i MOD rowlength # 0  THEN wl END;
END DisplayUsed;

PROCEDURE Garbage;
TYPE
  BlockAsSetsPtr = POINTER TO BlockAsSets;
  BlockAsSets = RECORD next, data: SET END;
VAR i: INTEGER; sp: BlockAsSetsPtr;
BEGIN
  wl; wsl("Garbage experiments.");
  wsl("Set all items garbage bit to zero.");
  FOR i := 0 TO LEN(Memory)-1 DO
    sp := SYSTEM.VAL(BlockAsSetsPtr, SYSTEM.ADR(Memory[i]));
    EXCL(sp^.next, 1)
  END;

  wsl("Mark Arg used.");
  Used(Arg);
  wsl("Mark Program used.");
  Used(Program);
  wsl("Mark Return used.");
  Used(Return);
  wsl("Mark Loop used.");
  Used(Loop);

  CountUsed;  ( * DisplayUsed * )
END Garbage;
*)

(* ----------------------------- Startup code ----------------------------- *)

BEGIN
  LineCount := 0;
  Assert(SYSTEM.VAL(Address, NIL) = 0, "Expected NIL to be zero.");
  ws("Address size is "); wi(SIZE(Address)*8); wsl(" bits.");
  InitMemory;

  InitLink(Boot, SYSTEM.VAL(Address, LoadBoostrap()));  (*DumpList(Boot);*)

  (* Run the bootstrap *)
  Program := Boot;  WHILE IsLink(Program) DO Step END;

  wl; ws("Bootstrap complete, "); DumpStack(Arg);

  (* Garbage detection *)
  (*
  Garbage
  *)
  MarkGarbage; ShowGarbage;

  TestFlattening

END dam.

