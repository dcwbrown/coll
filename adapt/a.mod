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


VAR
  Memory*: ARRAY AtomCount OF AtomDesc;
  Free*:   Atom;

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


PROCEDURE ExpandFlatValue*(VAR addr: Cell; VAR data: Cell);
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
END ExpandFlatValue;


(* ---------------------------- Atom navigation ----------------------------- *)

PROCEDURE FetchAtom*(link: Cell; VAR data, next: Cell);
CONST debug = FALSE;
VAR target: Atom;  param, addr, result: Cell;
BEGIN
  target := ATOM(link);

  IF debug THEN
    w.s("FetchAtom. link to "); w.x(link,1); w.l;
    IF target = NIL THEN
      w.sl("  target is NIL.")
    ELSE
      w.s("  target.next "); w.x(target.next, 16); w.l;
      w.s("  target.data "); w.x(target.data, 16); w.l;
    END
  END;

  IF target = NIL THEN
    next := 0; data := 0  (* Result is 0 integer atom. *)
  ELSIF KIND(target) < Flat THEN
    w.Assert(PARAM(link) = 0, "FetchAtom target is plain atom but link has nonzero parameter.");
    next := target.next;
    data := target.data
  ELSE
    param := PARAM(link);
    w.Assert(param < PARAM(target.data), "FetchAtom target is flat atom but link parameter addresses beyond flattened valuses.");
    addr := ADDR(target.data) + param;
    ExpandFlatValue(addr, data);
    param := addr - ADDR(target.data);
    IF param < PARAM(target.data) THEN
      next := link;
      SETPARAM(next, param)
    ELSE
      next := LINK(target.next)
    END
  END;

  IF debug THEN
    w.sl("  returning:");
    w.s("    next "); w.x(next, 16); w.l;
    w.s("    data "); w.x(data, 16); w.l
  END
END FetchAtom;

(* Fetch value of link to value of target atom. atom.next is unaffected. *)
PROCEDURE FetchValue*(link: Cell; atom: Atom);
CONST debug = FALSE;
VAR next: Cell;
BEGIN
  w.Assert(ADDR(link) # 0, "FetchValue passed NIL link.");
  FetchAtom(link, atom.data, next);
  SETKIND(atom, next MOD 4);

  IF debug THEN
    w.s("FetchValue. link to "); w.x(link,1); w.sl(", returned:");
    w.s("    next "); w.x(next, 16); w.l;
    w.s("    atom.next "); w.x(atom.next, 16); w.l;
    w.s("    atom.data "); w.x(atom.data, 16); w.l
  END;

END FetchValue;


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
