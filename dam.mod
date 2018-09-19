MODULE dam;  (* dam - data, algorithms and memory *)

IMPORT Files, TextWriter, SYSTEM, In;

CONST
  AtomCount  = 6000;
  StackDepth = 100;
  MaxBuffer  = 1024;
  MaxLines   = 8000;
  BlockSize  = 512; (* Max 2048 limited by Param field in next *)
  MinFlatRun = 4;

  (* Usage markings *)
  Unused   = 0;
  FlatUse  = 1;  (* Block referenced only once and only from 'next'. *)
  MultiUse = 2;

  (* Kinds *)
  Int  = 0;
  Link = 1;
  Flat = 2;  (* Internal to the implementation, not exposed to DAM code. *)

TYPE

  Address = SYSTEM.ADDRESS;  (* Integer of same size as address. *)
  Int8    = SYSTEM.INT8;

  AtomHeader = RECORD
    next: Address;  (* All headers 16 byte aligned. Bits are used as follows:
                         60/addr - Bits 63-4 of link to next next atom,
                                   bits 3-0 are always 0.
                                   The top bits of the link are used as
                                   a parameter - see below.
                         2/mark  - collection state of this atom
                         2/kind  - type of this atom - int/link/flat
                    *)
    data: Address;  (* Integer value, link address or flatlist limit. *)
    (* Flat list content immediately follows the header and continues
       to the limit stored in .data.
       Links (whether in the next or data field) have the form:
         1/unused - avoid conflict with signed operations
         11/param - of link e.g. offset from first byte of header into
                    compressed list
         52/addr  - Link address (up to 4.5 PB = 4500TB)
    *)
  END;
  AtomPtr* = POINTER [1] TO AtomHeader;

  (* Value can be a singular value, or the current value of a list. *)
  Value* = RECORD
    kind-:   Address;  (* Int or Link *)
    data-:   Address;  (* Integer value or adress of AtomHeader *)
    header-: AtomPtr;  (* Address of current AtomHeader if Link. *)
    (* Private cache for link into flatlist, 0 if not flat *)
    pos:     Address;  (* Address of this value, 0 if none, or not flat *)
    next:    Address;  (* Address of next value, 0 if none, or not flat *)
  END;

  ValueStack = RECORD
    stk: ARRAY StackDepth OF Value;
    top: INTEGER
  END;

  BlockPtr = POINTER TO Block;
  Block = RECORD
    bytes: ARRAY BlockSize OF Int8;
    next: BlockPtr;
    in: Address;
  END;

  AtomList = POINTER TO AtomListDesc;  (* For ListAll debugging dump. *)
  AtomListDesc = RECORD
    atom: Address;
    next: AtomList;
  END;

VAR
  LineCount: INTEGER;
  Memory:    ARRAY AtomCount OF AtomHeader;
  Free:      AtomPtr;

  Program: Value;

  Arg:    ValueStack;
  Return: ValueStack;

  IntrinsicVariable: ARRAY 26 OF Address;

  BootState:  INTEGER;
  BootNumber: INTEGER;
  BootStack:  ARRAY 10 OF AtomPtr;
  BootTop:    INTEGER;

  Blocks: BlockPtr;

  Lists: AtomList;  (* For ListAll debugging dump *)


(* ------------- C functions to access parts of the next field. ------------- *)

PROCEDURE- ATOMPTR(a: Address): AtomPtr "(dam_AtomPtr)((a) & 0x000FFFFFFFFFFFF0)";
PROCEDURE- PTR    (a: Address): Address "((a) & 0x000FFFFFFFFFFFF0)";
PROCEDURE- LINK   (a: Address): Address "((a) & 0x7FFFFFFFFFFFFFF0)";
PROCEDURE- KIND   (a: AtomPtr): Address "(((a)->next) & 3)";
PROCEDURE- USAGE  (a: AtomPtr): Address "((((a)->next)>>2) & 3)";
PROCEDURE- PARAM  (a: Address): Address "(((a)>>52) & 0x7FF)";

PROCEDURE- SETPTR  (VAR a: Address; p: AtomPtr) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x000000000000000F) | ((INT64)(p) & 0xFFFFFFFFFFFFFFF0))";
PROCEDURE- SETLINK (VAR a: Address; l: Address) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x000000000000000F) | ((l) & 0xFFFFFFFFFFFFFFF0))";
PROCEDURE- SETKIND (    a: AtomPtr; k: Address) "(a)->next = (((a)->next & 0xFFFFFFFFFFFFFFFC) | ((k) & 3))";
PROCEDURE- SETUSAGE(    a: AtomPtr; m: Address) "(a)->next = (((a)->next & 0xFFFFFFFFFFFFFFF3) | (((m) & 3) << 2))";
PROCEDURE- SETPARAM(VAR a: Address; p: Address) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x8000FFFFFFFFFFFF) | (((p) & (INT64)0x7FFF) << 52))";


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
BEGIN IF msg[0] # 0X THEN wlc; ws("Internal failure:"); wsl(msg) END;
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

PROCEDURE AlignUp(VAR addr: Address; unit: Address);
BEGIN
  addr := addr + unit-1;
  addr := addr - addr MOD unit;
END AlignUp;

PROCEDURE- BitwiseAnd(a,b: LONGINT): LONGINT "((a) & (b))";

PROCEDURE CompressValue(kind, data: Address; VAR buf: Block): BOOLEAN;
VAR val: ARRAY 12 OF Int8; i: INTEGER; success: BOOLEAN;
BEGIN success := FALSE;
  (*Assert(kind < 2, "CompressValue expected Int or Link type.");*)
  IF (kind = Int) & (data >= 0) & (data < 128) THEN
    (* The compressed values is just the data itself *)
    IF buf.in + 1 <= LEN(buf.bytes) THEN
      (*Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 0).");*)
      buf.bytes[buf.in] := SYSTEM.VAL(Int8, data);  INC(buf.in);
      success := TRUE
    END
  ELSE
    i := 0;
    REPEAT
      (*Assert(i < LEN(val), "i exceed buffer length (position 1");*)
      val[i] := SYSTEM.VAL(Int8, data MOD 128);
      data := data DIV 128;  (* Note, sign extends *)
      INC(i)
    UNTIL (i >= 10) OR (((data = -1) OR (data = 0)) & (i > 1));

    (* If there's not enough room for the type flag add one more byte. *)
    IF BitwiseAnd(val[i-1], 60H) # BitwiseAnd(data, 60H) THEN
      (*Assert(i < LEN(val), "i exceed buffer length (position 2");*)
      val[i] := SYSTEM.VAL(Int8, data); INC(i)
    END;

    IF buf.in + i <= LEN(buf.bytes) THEN
      DEC(i);
      (*Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 1).");*)
      buf.bytes[buf.in] := val[i] MOD 64 + SYSTEM.VAL(Int8, kind*64) + 127+1;
      INC(buf.in); DEC(i);
      WHILE i > 0 DO
        (*Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 2).");*)
        buf.bytes[buf.in] := val[i]+127+1;
        INC(buf.in); DEC(i)
      END;
      (*Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 3).");*)
      buf.bytes[buf.in] := val[0]; INC(buf.in);
      success := TRUE
    END
  END;
RETURN success END CompressValue;

PROCEDURE ExpandValue(addr: Address; VAR v: Value);
VAR byte: Int8; data: Address;
BEGIN
  v.pos := addr;
  SYSTEM.GET(addr, byte);
  IF byte >= 0 THEN
    v.kind := Int; v.data := byte
  ELSE
    v.kind := byte DIV 64 MOD 2;
    (* First byte of muti-byte value *)
    byte := byte * 4;  (* Sign extend 6 to 8 bits *)
    data := byte DIV 4;
    INC(addr);
    SYSTEM.GET(addr, byte);
    (* Middle bytes of multi-byte value *)
    WHILE byte < 0 DO
      data := data * 128  +  byte MOD 128;
      INC(addr);
      SYSTEM.GET(addr, byte)
    END;
    (* Last byte of multi-byte value *)
    v.data := data * 128 + byte
  END;
  INC(addr);
  Assert(addr <= v.header.data, "Decoded flat value extended past end of flat block.");
  IF addr < v.header.data THEN v.next := addr ELSE v.next := 0 END
END ExpandValue;


(* --------------------------------- Values --------------------------------- *)

PROCEDURE^ DumpHeader(addr: Address);

PROCEDURE wkind(k: Address);
BEGIN CASE k OF
  |Int:  ws("Int")
  |Link: ws("Link")
  |Flat: ws("Flat")
  ELSE   ws("invalid<"); wi(k); wc('>')
  END
END wkind;

PROCEDURE DumpValue(v: Value);
VAR link: Address;
BEGIN
  ws("DumpValue");
  ws(". Header at ");   wx(SYSTEM.VAL(Address, v.header), 16);
  IF v.header # NIL THEN
    ws(" ("); wx(v.header.next, 16); ws(", "); wx(v.header.data, 16); ws(")");
    wl;
    ws("  header usage "); wi(USAGE(v.header));
    ws(", header kind ");  wkind(KIND(v.header));
  END;
  ws(", current kind "); wkind(v.kind);
  ws(", current data "); wx(v.data, 1);
  IF v.pos # 0 THEN
    ws(", pos ");  wx(v.pos, 16);
    ws(", next "); wx(v.next, 16)
  END;
  wl;
  IF KIND(v.header) = Flat THEN
    wsl("Flat block ");
    link := SYSTEM.ADR(v.header.next);  SETPARAM(link, SIZE(AtomHeader));
    DumpHeader(link)
  END;
END DumpValue;

PROCEDURE InitInt(VAR v: Value; i: Address);
BEGIN
  v.kind   := Int;
  v.data   := i;
  v.header := NIL;
  v.pos    := 0;
  v.next   := 0;
END InitInt;

PROCEDURE CheckLink(s: ARRAY OF CHAR; link: Address);
VAR p: AtomPtr;
BEGIN
  p := ATOMPTR(link);
  IF (KIND(p) = Flat) & (PARAM(link) < SIZE(AtomHeader)) THEN
    wlc; ws(s); ws(", Invalid param in flatlist link = "); wx(link,16); wl;
  END
END CheckLink;

PROCEDURE InitLink(VAR v: Value; link: Address);
BEGIN
  CheckLink("InitLink", link);
  v.header := ATOMPTR(link);  Assert(v.header # NIL, "Cannot InitLink from NIL.");
  v.kind   := KIND(v.header);
  IF v.kind < Flat THEN
    v.data := v.header.data;
    v.pos  := 0;
    v.next := 0
  ELSE  (* Set up for link into flat list *)
    IF (PARAM(link) < SIZE(AtomHeader)) THEN
      ws("Link into flat list: "); wx(link,16); wl
    END;
    Assert(PARAM(link) >= SIZE(AtomHeader), "Expected link to flat list to reach past atom header.");
    Assert(PTR(link) + PARAM(link) < v.header.data, "Link into flat list has bad offset.");
    ExpandValue(PTR(link) + PARAM(link), v)
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
  ELSE
    CheckLink("Fetch", v.data);
    IF (v.pos # 0) & (PARAM(v.data) = 0) THEN
      Fail("Fetch link from storage block to workspace.")
    END;
    InitLink(v, v.data)
  END
END Fetch;

PROCEDURE Next*(VAR v: Value);
BEGIN
  Assert(IsLink(v), "Next expects reference that is a Link, not an Int.");
  IF v.next # 0 THEN  ExpandValue(v.next, v)
  ELSIF ATOMPTR(v.header.next) = NIL THEN InitInt(v, 0)
  ELSE
    CheckLink("Next", v.header.next);
    Assert((v.pos = 0) OR (PARAM(v.header.next) = 0), "Invalid next link from storage to workspace in next.");
    InitLink(v, v.header.next)
  END;
END Next;

PROCEDURE StoreValue(source: Value; VAR target: Value);
VAR a: AtomPtr;
BEGIN
  Assert(IsLink(target), "Target reference of Store must be a link.");
  IF KIND(target.header) = Flat THEN
    Fail("StoreValue target is in flat list but unflattening is not yet implemented.")
  END;
  IF IsLink(source) THEN
    (* target.header is the atom that we are updating. *)
    SETKIND(target.header, Link);
    target.header.data := SYSTEM.VAL(Address, source.header);
    IF source.pos # 0 THEN
      SETPARAM(target.header.data, source.pos - SYSTEM.VAL(Address, source.header))
    END;
    CheckLink("StoreValue", target.header.data);
    InitLink(target, target.header.data)
  ELSE
    SETKIND(target.header, Int);
    target.header.data := source.data;
    CheckLink("StoreValue", SYSTEM.VAL(Address, target.header));
    InitLink(target, SYSTEM.VAL(Address, target.header))
  END;
END StoreValue;


(* --------------------------------- Atoms --------------------------------- *)

PROCEDURE NewAtom(): AtomPtr;
VAR result: AtomPtr;
BEGIN
  Assert(Free # NIL, "Out of memory.");
  result := Free;  Free := ATOMPTR(Free.next);
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
  Memory[LEN(Memory)-1].data := 0;
  FOR i := 0 TO LEN(IntrinsicVariable)-1 DO IntrinsicVariable[i] := 0 END;
  Free := ATOMPTR(SYSTEM.ADR(Memory))
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


PROCEDURE wlink(link: Address);
VAR v: Value;
BEGIN
  ws("Link: "); wx(link,1); wsl(", value: ");
  InitLink(v, link); wvalue(v)
END wlink;


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
  (* Dump any remaining stack content *)
  IF stk.top = 0 THEN wsl("stack empty.")
  ELSE wsl("stack content:");
    Assert(stk.top >= 0, "Negative stack top index.");
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
    (*
    IF Program.data > 32 THEN ws("Intrinsic '"); wu(Program.data); wsl("'.") END;
    IF Program.data > 32 THEN wu(Program.data); wfl END;
    *)
    CASE CHR(Program.data) OF
    |' ', 0AX, 0DX: (* No op   *)

    (* Intrinsic global variables a..z and integer literals 0..F *)
    |'a'..'z':         Assert(Arg.top < StackDepth,
                              "intrinsic variable blocked because arg stack is full.");
                       i := Program.data - ORD('a');
                       IF IntrinsicVariable[i] = 0 THEN
                         IntrinsicVariable[i] := SYSTEM.VAL(Address, NewAtom())
                       END;
                       CheckLink("Variable address operation", IntrinsicVariable[i]);
                       InitLink(Arg.stk[Arg.top], IntrinsicVariable[i]); INC(Arg.top)
                       (*ws("Following initrinsic variable push, "); DumpStack(Arg); wl*)

    |'0'..'9':         Assert(Arg.top < StackDepth,
                              "Intrinsic literal blocked because arg stack is full.");
                       INC(Arg.top); InitInt(Arg.stk[Arg.top-1], Program.data - ORD('0'))

    |'A'..'F':         Assert(Arg.top < StackDepth,
                              "Intrinsic literal blocked because arg stack is full.");
                       INC(Arg.top); InitInt(Arg.stk[Arg.top-1], Program.data - ORD('A') + 10)

    |'`':              Assert(Arg.top < StackDepth,
                              "'`' literal blocked because arg stack is full.");
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
                         InitInt(Arg.stk[Arg.top-2],
                                 BoolVal(Arg.stk[Arg.top-1].header = Arg.stk[Arg.top-2].header))
                       ELSE
                         InitInt(Arg.stk[Arg.top-2],
                                 BoolVal(Arg.stk[Arg.top-1].data = Arg.stk[Arg.top-2].data))
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
                       InitInt(Arg.stk[Arg.top-2],
                               BoolVal(Truth(Arg.stk[Arg.top-2]) & Truth(Arg.stk[Arg.top-1])));
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

    (* Atom access *)
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
    |'!':(* Execute *) Assert(Return.top < StackDepth-1,
                              "Cannot enter nested list as return stack is full.");
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

(* Boot parse state:
     0 - normal
     1 - escaped
     2 - number
*)

PROCEDURE AddBootstrapAtom(VAR current: AtomPtr; data: Address);
BEGIN
  SETPTR(current.next, NewAtom());
  current := ATOMPTR(current.next);
  current.data := data
END AddBootstrapAtom;

PROCEDURE BootstrapAddChar(VAR current: AtomPtr;  ch: CHAR);
VAR link: AtomPtr;
BEGIN
  IF (BootState = 2) & ((ch < '0') OR (ch > '9')) THEN
    AddBootstrapAtom(current, BootNumber);
    BootState := 0;
  END;
  CASE BootState OF
  |0: CASE ch OF
      |'^': BootState := 1;
      |'[': AddBootstrapAtom(current, 0);  BootStack[BootTop] := current;  INC(BootTop);
      |']': DEC(BootTop);  link := BootStack[BootTop];
            link.data := LINK(link.next);
            link.next := Link;
            Assert(LINK(current.next) = 0, "Expected current.next to be at end of list in ']'.");
            current := link;
            link := ATOMPTR(link.data);
      ELSE  AddBootstrapAtom(current, ORD(ch))
      END
  |1: IF (ch >= '0') & (ch <= '9') THEN
        BootNumber := ORD(ch) - ORD('0');
        ws("Boot escaped number. First digit "); wi(BootNumber); wl;
        BootState := 2;
      ELSE
        AddBootstrapAtom(current, ORD(ch));
        BootState := 0
      END
  |2: BootNumber := BootNumber*10 + ORD(ch) - ORD('0')
  ELSE Fail("Invalid boot state.")
  END
END BootstrapAddChar;

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
  current := ATOMPTR(head.next);
RETURN current END LoadBoostrap;


(* --------------------------- Regroup debugging ---------------------------- *)

PROCEDURE whexbytes(VAR buf: ARRAY OF Int8; len: Address);
VAR i: Address;
BEGIN
  FOR i := 0 TO len-1 DO
    wx(buf[i],2);
    IF i < len-1 THEN wc(" ") END
  END
END whexbytes;

PROCEDURE ShowUsage;
CONST rowlength = 100;
VAR i: INTEGER;
BEGIN
  wsl("workspace atom usage:");
  i := 0; WHILE i < AtomCount DO
    IF i MOD rowlength = 0 THEN ws("  ") END;
    wc(CHR(USAGE(SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory[i]))) + ORD('0')));
    INC(i);
    IF i MOD rowlength = 0 THEN wl END
  END;
  IF i MOD rowlength # 0  THEN wl END;
END ShowUsage;

PROCEDURE DumpHeader(addr: Address);
VAR hdr: AtomPtr; val: Value;
BEGIN
  hdr := ATOMPTR(addr);
  ws("Header at ");  wx(addr, 16); wl;
  ws("  next: ");    wx(hdr.next,16);
  ws(" (usage ");    wi(USAGE(hdr));
  ws(", kind ");     wkind(KIND(hdr)); wsl(")");
  ws("  data: ");    wx(hdr.data,16);
  IF KIND(hdr) = Flat THEN
    ws(" => length "); wi(hdr.data - (PTR(addr) + SIZE(AtomHeader))); wsl(" bytes.")
  END;
  CheckLink("DumpHeader", addr);
  InitLink(val, addr);
  ws("  content: '");
  LOOP
    CASE val.kind OF
    |Int:  wu(val.data)
    |Link: wc("<"); wx(val.data,1); wc(">")
    ELSE ws("<bad kind "); wi(val.kind); ws(">")
    END;
    IF val.next = 0 THEN EXIT END;
    Next(val)
  END;
  wsl("'.");
END DumpHeader;

PROCEDURE DumpBlock(block: BlockPtr);
CONST BytesPerLine = 32;
VAR i: Address; addr: Address; hdr: AtomPtr;
BEGIN
  ws("Block at "); wx(SYSTEM.VAL(Address, block),16); wl;
  ws("  in:   "); wi(block.in); wl;
  ws("  next: "); wx(SYSTEM.VAL(Address, block.next),16); wl;

  (* Hex dump *)
  i := 0;
  WHILE i < block.in DO
    IF i MOD BytesPerLine = 0 THEN ws("  "); wx(i,4); ws(": ") END;
    wx(block.bytes[i],2); wc(" ");
    IF i MOD BytesPerLine = BytesPerLine - 1 THEN wl END;
    INC(i)
  END;
  IF i MOD BytesPerLine # 0 THEN wl END;

  (* Interpreted dump *)
  i := 0; WHILE i < block.in DO
    addr := SYSTEM.ADR(block.bytes[i]);
    SETPARAM(addr, SIZE(AtomHeader));
    wlc; DumpHeader(addr);
    hdr  := ATOMPTR(addr);
    i := hdr.data - SYSTEM.ADR(block.bytes);
    AlignUp(i, SIZE(AtomHeader));
  END;
END DumpBlock;


PROCEDURE DumpBlocks;
VAR block: BlockPtr;
BEGIN
  block := Blocks;
  WHILE block # NIL DO DumpBlock(block); block := block.next END
END DumpBlocks;

PROCEDURE CheckVariableUsages;
VAR i: INTEGER; v: Value;
BEGIN
  FOR i := 0 TO 25 DO
    IF IntrinsicVariable[i] # 0 THEN
      ws("Intrinsic '"); wu(ORD('a') + i); ws("' ");
      InitLink(v, IntrinsicVariable[i]);
      DumpValue(v)
    END
  END
END CheckVariableUsages;

PROCEDURE TestMakeFlatValue(t, a: Address; verbose: BOOLEAN);
VAR buf: Block; i: Address; v: Value;
  dummy: AtomHeader;
BEGIN
  IF verbose THEN wx(a,16) END;
  buf.in := 0;
  IF CompressValue(t, a, buf) THEN END;
  IF verbose THEN ws(" flattened: "); whexbytes(buf.bytes, buf.in) END;

  v.header := ATOMPTR(SYSTEM.ADR(dummy));
  dummy.data := SYSTEM.ADR(buf.bytes) + buf.in;
  ExpandValue(SYSTEM.ADR(buf.bytes), v);

  IF verbose THEN
    ws(", decoded: type "); wx(v.kind,1); ws(" data "); wx(v.data,16); wl
  END;
  Assert(t=v.kind,   "Flat value type lost.");
  Assert(a=v.data,   "Flat value data lost.");
  Assert(v.next = 0, "More bytes encoded than decoded.");
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

  TestMakeFlatValue(0, 01FFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(0, 01FFFFFFFFFFFFFFFH, TRUE);
  TestMakeFlatValue(0, 02000000000000000H, TRUE);
  TestMakeFlatValue(0, 02000000000000001H, TRUE);
  TestMakeFlatValue(0, 07FFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(0, 07FFFFFFFFFFFFFFFH, TRUE);
  TestMakeFlatValue(0, 08000000000000000H, TRUE);
  TestMakeFlatValue(0, 08000000000000001H, TRUE);
  TestMakeFlatValue(0, 0DFFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(0, 0DFFFFFFFFFFFFFFFH, TRUE);
  TestMakeFlatValue(0, 0E000000000000000H, TRUE);
  TestMakeFlatValue(0, 0E000000000000001H, TRUE);
  TestMakeFlatValue(0, 0FFFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(0, 0FFFFFFFFFFFFFFFFH, TRUE);
END TestFlattening;

PROCEDURE OutdatedTests;
BEGIN
  TestFlattening
END OutdatedTests;


(* --------------------------------- Regroup ---------------------------------*)

PROCEDURE WeighUsage(list: AtomPtr);
(* Note: No list in block storage may continue with or link to an atom
   in workspace memory. *)
BEGIN
  WHILE (list # NIL) & (KIND(list) < Flat) DO  (* Stops at first atom in block storage. *)
    IF (KIND(list) = Link) & (PARAM(list.data) = 0) THEN  (* Link into workspace *)
      WeighUsage(ATOMPTR(list.data))
    END;
    IF USAGE(list) = 0 THEN
      SETUSAGE(list, 1);
      list := ATOMPTR(list.next);
    ELSE
      SETUSAGE(list, 2);
      list := NIL
    END;
  END
END WeighUsage;


PROCEDURE NewFlatHeader(VAR hdr: AtomPtr);
VAR newblock: BlockPtr;
BEGIN
  IF Blocks # NIL THEN AlignUp(Blocks.in, SIZE(AtomHeader)) END;
  IF (Blocks = NIL) OR (Blocks.in + 32 > LEN(Blocks.bytes)) THEN
    NEW(newblock); newblock.in := 0; newblock.next := Blocks;
    Blocks := newblock
  END;
  hdr := ATOMPTR(SYSTEM.ADR(Blocks.bytes[Blocks.in]));
  INC(Blocks.in, SIZE(AtomHeader));
  hdr.next := Flat;
  hdr.data := 0
END NewFlatHeader;


PROCEDURE Storeable(a: AtomPtr): BOOLEAN;
BEGIN RETURN (KIND(a) < Flat)
           & ((KIND(a) # Link) OR (PARAM(a.data) # 0))
           & (USAGE(a) = FlatUse)
END Storeable;


PROCEDURE StoreRun(VAR link: Address);  (* Move run starting at link to block storage. *)
VAR l: AtomPtr; flatheader: AtomPtr;
BEGIN
  ws("Move run of atoms to block storage starting at link "); wx(link,1); wsl(".");
  Assert(Storeable(ATOMPTR(link)), "StoreRun passed unstoreable atom.");
  NewFlatHeader(flatheader);
  l := ATOMPTR(link);

  WHILE (l # NIL) & Storeable(l) & CompressValue(KIND(l), l.data, Blocks^) DO

    ws("Compressed atom at "); wx(SYSTEM.VAL(Address, l), 1);
    ws(": next "); wx(l.next, 1);  ws(": data "); wx(l.data, 1); wfl;

    SETUSAGE(l, 0);  (* l's content has moved, the original l is now free. *)
    l := ATOMPTR(l.next);

    ws(" .. next l "); wx(SYSTEM.VAL(Address, l), 1); wsl(".");
  END;

  Assert((l = NIL) OR (KIND(l) # Flat), "Cannot store run that continues in workspace memory.");
  SETLINK(flatheader.next, SYSTEM.VAL(Address, l));
  IF (l # NIL) & (KIND(l) = Flat) THEN SETPARAM(flatheader.next, SIZE(AtomHeader)) END;
  flatheader.data := SYSTEM.ADR(Blocks.bytes) + Blocks.in;

  ws("Link to workspace list was "); wx(link,1);
  SETPTR(link, flatheader);
  SETPARAM(link, SIZE(AtomHeader));
  ws(", now linked to block storage "); wx(link,1); wsl(".");
END StoreRun;


(* Chain moved as much as possible of a list into block storage.
   The rule is that atoms in block storage may not point back into workspace
   memory either through their next pointer or as a Link.
   Therefore before attempting to move the chain we have been passed, we
   first move any lists it links to.
   Secondly we move chains at the the end of the list before those
   earlier on.
 *)
PROCEDURE Chain(VAR list: Address);  (* Usually passed the next or data field of an atomheader. *)
VAR prev, storeable, l: AtomPtr; i: INTEGER;
BEGIN
  ws("Chain("); wx(list,1); wsl(")");
  Assert(PARAM(list) = 0, "Chain expects to be passed link to list in workspace.");
  Assert(KIND(ATOMPTR(list)) < Flat, "Chain expects to be passed link to non-flat atom.");

  (* First try moving flatteneable parts of sublists to block storage. In the
     process record the first storeable atom. *)
  l := ATOMPTR(list);  storeable := NIL;
  prev := SYSTEM.VAL(AtomPtr, SYSTEM.ADR(list));
  WHILE (l # NIL) & (KIND(l) < Flat) DO
    IF (KIND(l) = Link) & (USAGE(l) = FlatUse) & (PARAM(l.data) = 0) THEN
      Chain(l.data);
    END;
    ws("Test storeability. prev "); wx(SYSTEM.VAL(Address, prev),1);
    ws(", l "); wx(SYSTEM.VAL(Address, l),1);
    ws(", USAGE "); wi(USAGE(l));
    ws(", KIND "); wkind(KIND(l));
    ws(", data "); wx(l.data,1);
    ws(", Storable(l) "); wb(Storeable(l));
    wsl(".");
    IF Storeable(l) THEN
      IF storeable = NIL THEN storeable := prev END
    ELSE
      storeable := NIL;
    END;
    prev := l;
    l := ATOMPTR(l.next)
  END;

  IF (storeable # NIL) & ((l = NIL) OR (KIND(l) = Flat)) THEN
    (* Are there enough chainable atoms to make it worthwhile? *)
    (*
    i := 0;
    l := ATOMPTR(storeable.next);
    WHILE (l # NIL) & (i < MinFlatRun) DO
      Assert(Storeable(l), "Unstoreable atom in run (incorrectly) found to be storeable.");
      l := ATOMPTR(l.next);  INC(i)
    END;

    IF i >= MinFlatRun THEN
    *)
      StoreRun(storeable.next)
    (*
    ELSE
      ws(".. Not storing list "); wx(list,1);
      ws(" as storeable length only "); wi(i); wsl(".")
    END
    *)
  ELSE
    ws(".. Nothing to store from list "); wx(list,1);
    ws(": storeable "); wx(SYSTEM.VAL(Address, storeable),1);
    ws(", l "); wx(SYSTEM.VAL(Address, l),1); wsl(".");
  END
END Chain;


PROCEDURE ReclaimUnusedAtoms;
VAR i: Address;
BEGIN
  Free := NIL;
  FOR i := 0 TO AtomCount-1 DO
    IF USAGE(SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory[i]))) = 0 THEN
      Memory[i].next := SYSTEM.VAL(Address, Free);
      Memory[i].data := 0;
      SETUSAGE(SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory[i])), 3);
      Free := SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory[i]));
    END
  END
END ReclaimUnusedAtoms;


PROCEDURE RegroupAndCollect;
VAR i: Address; flatheader: AtomPtr; link: Address;
BEGIN
  (* Initialise all workspace atom usage counts to zero *)
  FOR i := 0 TO AtomCount-1 DO SETUSAGE(SYSTEM.VAL(AtomPtr, SYSTEM.ADR(Memory[i])), 0) END;

  ws("Boot usage initially "); wi(USAGE(ATOMPTR(IntrinsicVariable[25]))); wl;

  (* Weigh all lists beginning at intrinisic variables. *)
  FOR i := 0 TO 25 DO
    IF IntrinsicVariable[i] # 0 THEN
      WeighUsage(ATOMPTR(IntrinsicVariable[i]))
    END
  END;

  ws("Boot link usage after WeighUsage "); wi(USAGE(ATOMPTR(IntrinsicVariable[25]))); wl;

  ws("After weighing, before chaining ");
  ShowUsage;
  CheckVariableUsages;

  (* Chain all lists beginning at intrinisic variables. *)
  FOR i := 0 TO 25 DO
    IF IntrinsicVariable[i] # 0 THEN
      Chain(IntrinsicVariable[i])
    END
  END;

  ws("After chaining before reclaiming ");
  ShowUsage;
  CheckVariableUsages;

  (*
  ReclaimUnusedAtoms;

  ws("After reclaiming ");
  ShowUsage
  *)

END RegroupAndCollect;

(* --- *)


(* ---------------------- Formatted list of all atoms --------------------- *)

PROCEDURE AddList(l: Address);
VAR list: AtomList;  v: Value;
BEGIN
  IF l # 0 THEN
    list := Lists;  (* Check first whether this list is already recorded *)
    WHILE (list # NIL) & (list.atom # l) DO list := list.next END;

    IF list = NIL THEN
      (* List is not already recorded, add it. *)
      NEW(list);
      list.atom := l;

      InitLink(v, l);
      WHILE IsLink(v) DO
        IF v.kind = Link THEN AddList(v.data) END;
        Next(v)
      END;

      list.next := Lists;  Lists := list
    END
  END
END AddList;

PROCEDURE NameList(link: Address): CHAR;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO 25 DO
    IF IntrinsicVariable[i] = link THEN RETURN CHR(ORD('a') + i) END
  END;
  RETURN ' '
END NameList;

PROCEDURE ListList(link: Address);
VAR v: Value; inworkspace: BOOLEAN;
BEGIN inworkspace := TRUE;
  wc(NameList(link)); wc(" ");
  wx(link,16); ws(": ");
  InitLink(v, link);
  WHILE IsLink(v) DO
    IF (v.pos = 0) # inworkspace THEN
      IF v.pos # 0 THEN wc('{') ELSE wc('}') END;
      inworkspace := v.pos = 0;
    END;
    IF v.kind = Link THEN
      wc("<"); wx(v.data,1); wc(">")
    ELSE
      CASE v.data OF
      |0AH: ws("<l>")
      |0DH:
      |20H:
      ELSE wu(v.data)
      END
    END;
    Next(v);
  END;
  IF ~inworkspace THEN wc("}") END;
  wl
END ListList;

PROCEDURE ListAll;
VAR i: INTEGER; l: AtomList;
BEGIN
  Lists := NIL;
  FOR i := 0 TO 25 DO AddList(IntrinsicVariable[i]) END;
  l := Lists;
  WHILE l # NIL DO ListList(l.atom); l := l.next END
END ListAll;




(* ----------------------------- Startup code ----------------------------- *)

BEGIN
  LineCount := 0;
  Assert(SYSTEM.VAL(Address, NIL) = 0, "Expected NIL to be zero.");
  ws("Address size is "); wi(SIZE(Address)*8); wsl(" bits.");
  InitMemory;

  (* Load the bootstrap as intrinsic variable 'z'. *)
  IntrinsicVariable[25] := SYSTEM.VAL(Address, LoadBoostrap());

  (* Run the bootstrap *)
  wsl("Running bootstrap before regroup.");
  InitLink(Program, IntrinsicVariable[25]);
  WHILE IsLink(Program) DO Step END;
  wlc; ws("Bootstrap complete, "); DumpStack(Arg);

  RegroupAndCollect;

  wl; wsl("List of all lists after first RegroupAndCollect:");
  ListAll; wl;

  wsl("Dump of Boot after first RegroupAndCollect:");
  wlink(IntrinsicVariable[25]);

  wsl("Run bootstrap after first RegroupAndCollect.");
  InitLink(Program, IntrinsicVariable[25]);
  WHILE IsLink(Program) DO Step END;

  RegroupAndCollect;
  ws("Usage after second RegroupAndCollect, "); ShowUsage;

  wsl("Dump of Boot after second RegroupAndCollect:");
  wlink(IntrinsicVariable[25]);

  wsl("Run bootstrap after second RegroupAndCollect.");
  InitLink(Program, IntrinsicVariable[25]);
  WHILE IsLink(Program) DO Step END;

END dam.

