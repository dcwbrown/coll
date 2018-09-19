MODULE a;  (* a (atom) - core data structure for adapt. *)

IMPORT w, SYSTEM;

CONST
  AtomCount* = 6000;
  MaxBuffer  = 1024;
  BlockSize  = 512; (* Max 2048 limited by Param field in next *)

  (* Usage markings *)
  Unused*   = 0;
  FlatUse*  = 1;  (* Block referenced only once and only from 'next'. *)
  MultiUse* = 2;

  (* Kinds *)
  Int*  = 0;
  Link* = 1;
  Flat* = 2;  (* Internal to the implementation, not exposed to atom code. *)

TYPE

  Address* = SYSTEM.ADDRESS;  (* Integer of same size as address. *)
  Int8*    = SYSTEM.INT8;

  AtomHeader* = RECORD
    next*: Address;  (* All headers 16 byte aligned. Bits are used as follows:
                          60/addr - Bits 63-4 of link to next next atom,
                                    bits 3-0 are always 0.
                                    The top bits of the link are used as
                                    a parameter - see below.
                          2/mark  - collection state of this atom
                          2/kind  - type of this atom - int/link/flat
                     *)
    data*: Address;  (* Integer value, link address or flatlist limit. *)
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
    header*: AtomPtr;  (* Address of current AtomHeader if Link. *)
    (* Private cache for link into flatlist, 0 if not flat *)
    pos-:    Address;  (* Address of this value, 0 if none, or not flat *)
    next-:   Address;  (* Address of next value, 0 if none, or not flat *)
  END;

  BlockPtr* = POINTER TO Block;
  Block* = RECORD
    bytes-: ARRAY BlockSize OF Int8;
    next-:  BlockPtr;
    in*:    Address;
  END;

VAR
  Memory-: ARRAY AtomCount OF AtomHeader;
  Free:    AtomPtr;

  IntrinsicVariable*: ARRAY 26 OF Address;

  Blocks-: BlockPtr;


(* ------------- C functions to access parts of the next field. ------------- *)

PROCEDURE- ATOMPTR*(a: Address): AtomPtr "(a_AtomPtr)((a) & 0x000FFFFFFFFFFFF0)";
PROCEDURE- PTR*    (a: Address): Address "((a) & 0x000FFFFFFFFFFFF0)";
PROCEDURE- LINK*   (a: Address): Address "((a) & 0x7FFFFFFFFFFFFFF0)";
PROCEDURE- KIND*   (a: AtomPtr): Address "(((a)->next) & 3)";
PROCEDURE- USAGE*  (a: AtomPtr): Address "((((a)->next)>>2) & 3)";
PROCEDURE- PARAM*  (a: Address): Address "(((a)>>52) & 0x7FF)";

PROCEDURE- SETPTR*  (VAR a: Address; p: AtomPtr) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x000000000000000F) | ((INT64)(p) & 0xFFFFFFFFFFFFFFF0))";
PROCEDURE- SETLINK* (VAR a: Address; l: Address) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x000000000000000F) | ((l) & 0xFFFFFFFFFFFFFFF0))";
PROCEDURE- SETKIND* (    a: AtomPtr; k: Address) "(a)->next = (((a)->next & 0xFFFFFFFFFFFFFFFC) | ((k) & 3))";
PROCEDURE- SETUSAGE*(    a: AtomPtr; m: Address) "(a)->next = (((a)->next & 0xFFFFFFFFFFFFFFF3) | (((m) & 3) << 2))";
PROCEDURE- SETPARAM*(VAR a: Address; p: Address) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x8000FFFFFFFFFFFF) | (((p) & (INT64)0x7FFF) << 52))";


(* ---------------------------- FLattened values ---------------------------- *)

PROCEDURE AlignUp*(VAR addr: Address; unit: Address);
BEGIN
  addr := addr + unit-1;
  addr := addr - addr MOD unit;
END AlignUp;

PROCEDURE- BitwiseAnd(a,b: LONGINT): LONGINT "((a) & (b))";

PROCEDURE CompressValue*(kind, data: Address; VAR buf: Block): BOOLEAN;
VAR val: ARRAY 12 OF Int8; i: INTEGER; success: BOOLEAN;
BEGIN success := FALSE;
  (*w.Assert(kind < 2, "CompressValue expected Int or Link type.");*)
  IF (kind = Int) & (data >= 0) & (data < 128) THEN
    (* The compressed values is just the data itself *)
    IF buf.in + 1 <= LEN(buf.bytes) THEN
      (*w.Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 0).");*)
      buf.bytes[buf.in] := SYSTEM.VAL(Int8, data);  INC(buf.in);
      success := TRUE
    END
  ELSE
    i := 0;
    REPEAT
      (*w.Assert(i < LEN(val), "i exceed buffer length (position 1");*)
      val[i] := SYSTEM.VAL(Int8, data MOD 128);
      data := data DIV 128;  (* Note, sign extends *)
      INC(i)
    UNTIL (i >= 10) OR (((data = -1) OR (data = 0)) & (i > 1));

    (* If there's not enough room for the type flag add one more byte. *)
    IF BitwiseAnd(val[i-1], 60H) # BitwiseAnd(data, 60H) THEN
      (*w.Assert(i < LEN(val), "i exceed buffer length (position 2");*)
      val[i] := SYSTEM.VAL(Int8, data); INC(i)
    END;

    IF buf.in + i <= LEN(buf.bytes) THEN
      DEC(i);
      (*w.Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 1).");*)
      buf.bytes[buf.in] := val[i] MOD 64 + SYSTEM.VAL(Int8, kind*64) + 127+1;
      INC(buf.in); DEC(i);
      WHILE i > 0 DO
        (*w.Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 2).");*)
        buf.bytes[buf.in] := val[i]+127+1;
        INC(buf.in); DEC(i)
      END;
      (*w.Assert(buf.in < LEN(buf.bytes), "buf.in exceeds buffer length (position 3).");*)
      buf.bytes[buf.in] := val[0]; INC(buf.in);
      success := TRUE
    END
  END;
RETURN success END CompressValue;

PROCEDURE ExpandValue*(addr: Address; VAR v: Value);
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
  w.Assert(addr <= v.header.data, "Decoded flat value extended past end of flat block.");
  IF addr < v.header.data THEN v.next := addr ELSE v.next := 0 END
END ExpandValue;


(* --------------------------------- Values --------------------------------- *)

PROCEDURE InitInt*(VAR v: Value; i: Address);
BEGIN
  v.kind   := Int;
  v.data   := i;
  v.header := NIL;
  v.pos    := 0;
  v.next   := 0;
END InitInt;

PROCEDURE CheckLink*(s: ARRAY OF CHAR; link: Address);
VAR p: AtomPtr;
BEGIN
  p := ATOMPTR(link);
  IF (KIND(p) = Flat) & (PARAM(link) < SIZE(AtomHeader)) THEN
    w.lc; w.s(s); w.s(", Invalid param in flatlist link = "); w.x(link,16); w.l;
  END
END CheckLink;

PROCEDURE InitLink*(VAR v: Value; link: Address);
BEGIN
  CheckLink("InitLink", link);
  v.header := ATOMPTR(link);  w.Assert(v.header # NIL, "Cannot InitLink from NIL.");
  v.kind   := KIND(v.header);
  IF v.kind < Flat THEN
    v.data := v.header.data;
    v.pos  := 0;
    v.next := 0
  ELSE  (* Set up for link into flat list *)
    IF (PARAM(link) < SIZE(AtomHeader)) THEN
      w.s("Link into flat list: "); w.x(link,16); w.l
    END;
    w.Assert(PARAM(link) >= SIZE(AtomHeader), "Expected link to flat list to reach past atom header.");
    w.Assert(PTR(link) + PARAM(link) < v.header.data, "Link into flat list has bad offset.");
    ExpandValue(PTR(link) + PARAM(link), v)
  END
END InitLink;

PROCEDURE IsLink*(VAR v: Value): BOOLEAN;
BEGIN RETURN v.header # NIL END IsLink;

PROCEDURE Truth*(VAR v: Value): BOOLEAN;
BEGIN RETURN IsLink(v) OR (v.data # 0) END Truth;

PROCEDURE Fetch*(VAR v: Value);
BEGIN
  w.Assert(IsLink(v), "Fetch expects reference that is a Link, not an Int.");
  IF v.kind = Int THEN InitInt(v, v.data)
  ELSE
    CheckLink("Fetch", v.data);
    IF (v.pos # 0) & (PARAM(v.data) = 0) THEN
      w.Fail("Fetch link from storage block to workspace.")
    END;
    InitLink(v, v.data)
  END
END Fetch;

PROCEDURE Next*(VAR v: Value);
BEGIN
  w.Assert(IsLink(v), "Next expects reference that is a Link, not an Int.");
  IF v.next # 0 THEN  ExpandValue(v.next, v)
  ELSIF ATOMPTR(v.header.next) = NIL THEN InitInt(v, 0)
  ELSE
    CheckLink("Next", v.header.next);
    w.Assert((v.pos = 0) OR (PARAM(v.header.next) = 0), "Invalid next link from storage to workspace in next.");
    InitLink(v, v.header.next)
  END;
END Next;

PROCEDURE StoreValue*(source: Value; VAR target: Value);
VAR a: AtomPtr;
BEGIN
  w.Assert(IsLink(target), "Target reference of Store must be a link.");
  IF KIND(target.header) = Flat THEN
    w.Fail("StoreValue target is in flat list but unflattening is not yet implemented.")
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

PROCEDURE NewAtom*(): AtomPtr;
VAR result: AtomPtr;
BEGIN
  w.Assert(Free # NIL, "Out of memory.");
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



BEGIN InitMemory
END a.

