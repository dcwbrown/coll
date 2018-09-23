MODULE a;  (* a (atom) - core data structure for adapt. *)

IMPORT w, SYSTEM;

CONST
  AtomCount* = 6000;
  MaxBuffer  = 1024;
  BlockSize  = 512; (* Max 2048 limited by Param field in next. *)

  (* Usage markings *)
  Unreferenced* = 0;
  Stackable*    = 1;  (* Block referenced only once. *)
  Unstackable*  = 2;

  (* Kinds - encoded as the bottom 2 bits of the next field of every atom. *)
  Int*  = 0;
  Link* = 1;
  Flat* = 2;  (* Internal to the implementation, not exposed to atom code. *)

TYPE

  Cell* = SYSTEM.ADDRESS;  (* Integer of same size as address. *)
  Int8* = SYSTEM.INT8;

  AtomDesc* = RECORD
    next*: Cell;  (* All headers 16 byte aligned. Bits are used as follows:
                          60/addr - Bits 63-4 of link to next next atom,
                                    bits 3-0 are always 0.
                                    The top bits of the link are used as
                                    a parameter - see below.
                          2/mark  - collection state of this atom
                          2/kind  - type of this atom - int/link/flat
                  *)
    data*: Cell;  (* Integer value, link address or flatlist limit. *)
    (* Cell format:
         Int Cell:   64/integer value
         Link cell:  12/offset, 52/atom address (of flat atom)
         Flat cell:  12/length, 52/byte address (of compressed integers)
    *)
  END;
  Atom* = POINTER [1] TO AtomDesc;  (* Not garbage collected by Oberon RTS *)

  (* Value can be a singular value, or the current value of a list. *)
  Value* = RECORD
    kind-: Cell;  (* Int or Link. *)
    data-: Cell;  (* Integer value or adress of AtomDesc. *)
    atom*: Atom;  (* Cell of current AtomDesc if Link. *)
    (* Private cache for link into flatlist, 0 if not flat. *)
    pos-:  Cell;  (* Address of this value, 0 if none, or not flat. *)
    next-: Cell;  (* Address of next value, 0 if none, or not flat. *)
    lim-:  Cell;  (* Limit address of data referenced by atom. *)
  END;

VAR
  Memory*: ARRAY AtomCount OF AtomDesc;
  Free*:    Atom;

  IntrinsicVariable*: ARRAY 26 OF Cell;


(* ------------- C functions to access parts of the next field. ------------- *)

PROCEDURE- ATOM* (a: Cell): Atom "(a_Atom)((a) & 0x000FFFFFFFFFFFF0)";
PROCEDURE- ADDR* (a: Cell): Cell "((a) & 0x000FFFFFFFFFFFF0)";
PROCEDURE- LINK* (a: Cell): Cell "((a) & 0xFFFFFFFFFFFFFFF0)";
PROCEDURE- KIND* (a: Atom): Cell "(((a)->next) & 3)";
PROCEDURE- USAGE*(a: Atom): Cell "((((a)->next)>>2) & 3)";
PROCEDURE- PARAM*(a: Cell): Cell "(((a)>>52) & 0xFFF)";

PROCEDURE- SETADDR* (VAR a: Cell; p: Atom) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x000000000000000F) | ((INT64)(p) & 0xFFFFFFFFFFFFFFF0))";
PROCEDURE- SETLINK* (VAR a: Cell; l: Cell) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x000000000000000F) | ((l) & 0xFFFFFFFFFFFFFFF0))";
PROCEDURE- SETKIND* (    a: Atom; k: Cell) "(a)->next = (((a)->next & 0xFFFFFFFFFFFFFFFC) | ((k) & 3))";
PROCEDURE- SETUSAGE*(    a: Atom; m: Cell) "(a)->next = (((a)->next & 0xFFFFFFFFFFFFFFF3) | (((m) & 3) << 2))";
PROCEDURE- SETPARAM*(VAR a: Cell; p: Cell) "*((INT64*)(a)) = ((*((INT64*)(a)) & 0x0000FFFFFFFFFFFF) | (((p) & (INT64)0xFFFF) << 52))";


(* ---------------------------- FLattened values ---------------------------- *)


PROCEDURE Expand*(VAR addr: Cell; VAR data: Cell);
VAR byte: Int8; accumulator: Cell;
BEGIN
  SYSTEM.GET(addr, byte);
  IF byte >= 0 THEN
    accumulator := byte
  ELSE
    (* First (most significant) byte of muti-byte value *)
    byte := byte * 2;  (* Sign extend 7 to 8 bits *)
    accumulator := byte DIV 2;
    INC(addr);
    SYSTEM.GET(addr, byte);
    (* Middle bytes of multi-byte value *)
    WHILE byte < 0 DO
      accumulator := accumulator * 128  +  byte MOD 128;
      INC(addr);
      SYSTEM.GET(addr, byte)
    END;
    (* Last byte of multi-byte value *)
    accumulator := accumulator * 128 + byte
  END;
  INC(addr);
  data := accumulator;
END Expand;

PROCEDURE ExpandValue(addr: Cell; VAR v: Value);
BEGIN
  w.Assert(addr < v.lim, "InitLink: link offset beyond target compressed bytes.");
  v.pos := addr;
  v.kind := Int;
  Expand(addr, v.data);
  w.Assert(addr <= v.lim, "Decoded flat value extended past end of flat block.");
  IF addr < v.lim THEN v.next := addr ELSE v.next := 0 END
END ExpandValue;


(* --------------------------------- Values --------------------------------- *)

PROCEDURE InitInt*(VAR v: Value; i: Cell);
BEGIN
  v.kind := Int;
  v.data := i;
  v.atom := NIL;
  v.pos  := 0;
  v.next := 0;
  v.lim  := 0;
END InitInt;

PROCEDURE InitLink*(VAR v: Value; link: Cell);
BEGIN
  v.atom := ATOM(link);  w.Assert(v.atom # NIL, "Cannot InitLink from NIL.");
  v.kind := KIND(v.atom);
  IF v.kind < Flat THEN
    v.data := v.atom.data;
    v.pos  := 0;
    v.next := 0;
    v.lim  := 0;
  ELSE  (* Set up for link into flat list *)
    v.lim := v.atom.data MOD 10000000000000H + PARAM(v.atom.data);
    ExpandValue(v.atom.data MOD 10000000000000H + PARAM(link), v)
  END
END InitLink;

PROCEDURE IsLink*(VAR v: Value): BOOLEAN;
BEGIN RETURN v.atom # NIL END IsLink;

PROCEDURE Truth*(VAR v: Value): BOOLEAN;
BEGIN RETURN IsLink(v) OR (v.data # 0) END Truth;

PROCEDURE Next*(VAR v: Value);
BEGIN
  w.Assert(IsLink(v), "Next expects reference that is a Link, not an Int.");
  IF v.next # 0 THEN ExpandValue(v.next, v)
  ELSIF ATOM(v.atom.next) = NIL THEN InitInt(v, 0)
  ELSE InitLink(v, v.atom.next)
  END;
END Next;

PROCEDURE Fetch*(VAR v: Value);
BEGIN
  w.Assert(IsLink(v), "Fetch expects reference that is a Link, not an Int.");
  IF v.kind = Int THEN InitInt(v, v.data)
  ELSE InitLink(v, v.data)
  END
END Fetch;

PROCEDURE StoreValue*(source: Value; VAR target: Value);
VAR a: Atom;
BEGIN
  w.Assert(IsLink(target), "Target reference of Store must be a link.");
  IF KIND(target.atom) = Flat THEN
    w.Fail("StoreValue target is in flat list but unflattening is not yet implemented.")
  END;
  IF IsLink(source) THEN
    (* target.atom is the atom that we are updating. *)
    SETKIND(target.atom, Link);
    target.atom.data := SYSTEM.VAL(Cell, source.atom);
    IF source.pos # 0 THEN
      SETPARAM(target.atom.data, source.pos - source.atom.data MOD 10000000000000H)
    END;
    InitLink(target, target.atom.data)
  ELSE
    SETKIND(target.atom, Int);
    target.atom.data := source.data;
    InitLink(target, SYSTEM.VAL(Cell, target.atom))
  END;
END StoreValue;


(* --------------------------------- Atoms --------------------------------- *)

PROCEDURE NewAtom*(): Atom;
VAR result: Atom;
BEGIN
  w.Assert(Free # NIL, "Out of memory.");
  result := Free;  Free := ATOM(Free.next);
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
  Free := ATOM(SYSTEM.ADR(Memory))
END InitMemory;



BEGIN InitMemory
END a.
