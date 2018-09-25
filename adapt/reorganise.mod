MODULE reorganise;  (* reorganise - data, algorithms and memory *)

IMPORT w, a, dumping, SYSTEM;

CONST
  BlockSize  = 512; (* Max 2048 limited by Param field in next *)

TYPE
  Block* = POINTER TO BlockDesc;
  BlockDesc* = RECORD
    bytes-: ARRAY BlockSize OF a.Int8;
    next-:  Block;
    in*:    a.Cell;
  END;

VAR
  Blocks-: Block;


(* ---------------------------- FLattened values ---------------------------- *)

PROCEDURE- BitwiseAnd(a,b: LONGINT): LONGINT "((a) & (b))";

PROCEDURE Compress*(data: a.Cell; VAR buf: Block): BOOLEAN;
VAR val: ARRAY 12 OF a.Int8; i: INTEGER; success: BOOLEAN;
BEGIN success := FALSE;
  IF (data >= 0) & (data < 128) THEN  (* The compressed values is just the data itself *)
    IF buf.in + 1 <= LEN(buf.bytes) THEN
      buf.bytes[buf.in] := SYSTEM.VAL(a.Int8, data);  INC(buf.in);
      success := TRUE
    END
  ELSE
    i := 0;
    REPEAT
      val[i] := SYSTEM.VAL(a.Int8, data MOD 128);
      data := data DIV 128;  (* Note, sign extends *)
      INC(i)
    UNTIL (i >= 10) OR (((data = -1) OR (data = 0)) & (i > 1));

    (* If the top compressed bit is different from the sign add one more byte. *)
    IF BitwiseAnd(val[i-1], 40H) # BitwiseAnd(data, 40H) THEN
      val[i] := SYSTEM.VAL(a.Int8, data MOD 128); INC(i)
    END;

    IF buf.in + i <= LEN(buf.bytes) THEN
      DEC(i);
      WHILE i > 0 DO
        buf.bytes[buf.in] := val[i]+127+1;
        INC(buf.in); DEC(i)
      END;
      buf.bytes[buf.in] := val[0]; INC(buf.in);
      success := TRUE
    END
  END;
RETURN success END Compress;


(* --------------------------------- Regroup ---------------------------------*)

PROCEDURE RegisterListUsage(atom: a.Atom);
VAR usage: INTEGER;
BEGIN
  usage := a.Unstackable;  (* The first node cannot be compressed *)
  WHILE (atom # NIL) & (a.USAGE(atom) = a.Unreferenced) DO
    IF a.KIND(atom) = a.Link THEN
      RegisterListUsage(a.ATOM(atom.data));
      usage := a.Unstackable;
    END;
    a.SETUSAGE(atom, usage);
    atom := a.ATOM(atom.next);
    usage := a.Stackable  (* Subsequent Int nodes can be compressed. *)
  END;
  IF atom # NIL THEN a.SETUSAGE(atom, a.Unstackable) END
END RegisterListUsage;


PROCEDURE StackRun(first: a.Atom);  (* Comress run starting at 'first' to block storage. *)
VAR l: a.Atom; addr: a.Cell; newblock: Block;
BEGIN
  w.Assert(a.USAGE(first) = a.Stackable, "StackRun passed unstackable atom.");

  IF a.KIND(first) # a.Int THEN
    w.s("StackRun passed non-Int kind atom:");
    dumping.DumpHeader(SYSTEM.ADR(first^));
  END;
  w.Assert(a.KIND(first) = a.Int, "StackRun passed non-Int kind atom.");

  (* Start new block as necessary. *)
  IF Blocks = NIL THEN NEW(Blocks); Blocks.in := 0 END;
  IF Blocks.in + 2 > LEN(Blocks.bytes) THEN
    NEW(newblock); newblock.in := 0; newblock.next := Blocks;
    Blocks := newblock
  END;
  addr := SYSTEM.ADR(Blocks.bytes[Blocks.in]);

  l := first;
  WHILE (l # NIL)
      & (a.KIND(l) = a.Int)
      & (a.USAGE(l) = a.Stackable)
      & Compress(l.data, Blocks) DO
    a.SETUSAGE(l, 0);  (* l's content has moved, the original l is now free. *)
    l := a.ATOM(l.next);
  END;

  w.Assert(l # first, "StackRun failed to compress any atoms at all.");
  w.Assert(l # a.ATOM(first.next), "StackRun compressed only one atom.");

  (* Change first to reference the whole compressed list. *)
  a.SETKIND(first, a.Flat);
  a.SETUSAGE(first, a.Unstackable);
  a.SETADDR(first.next, l);
  first.data := addr;
  a.SETPARAM(first.data, SYSTEM.ADR(Blocks.bytes) + Blocks.in - addr);
END StackRun;


PROCEDURE WriteFlatAtom(atom: a.Atom);
VAR addr, limit, data: a.Cell;
BEGIN
  addr  := atom.data MOD 10000000000000H;
  limit := addr + a.PARAM(atom.data);
  WHILE addr < limit DO
    a.Expand(addr, data);
    IF data < 32 THEN w.c('<'); w.i(data); w.c('>'); w.nb ELSE w.u(data) END
  END;
  w.Assert(addr = limit, "Flat atom content did not end exactly at limit.");
END WriteFlatAtom;

PROCEDURE Stackable(atom: a.Atom): BOOLEAN;
BEGIN RETURN (a.USAGE(atom) = a.Stackable)
           & (a.KIND(atom)  = a.Int)
END Stackable;

PROCEDURE StackList(first: a.Atom);
VAR l, m: a.Atom; count: a.Cell;
BEGIN
  l := first;  (* First stack sublists *)
  WHILE l # NIL DO
    IF a.KIND(l) = a.Link THEN StackList(a.ATOM(l.data)) END;
    l := a.ATOM(l.next)
  END;
  l := first;  (* Now stack runs within this list *)
  WHILE l # NIL DO
    WHILE (l # NIL) & ~Stackable(l) DO l := a.ATOM(l.next) END;
    m := l;  count := 0;
    WHILE (m # NIL) & Stackable(m) & (count < 3) DO
      m := a.ATOM(m.next); INC(count)
    END;
    IF count > 2 THEN StackRun(l); l := a.ATOM(l.next); ELSE l := m END
  END
END StackList;


PROCEDURE RecycleUnusedAtoms;
VAR i: a.Cell;
BEGIN
  a.Free := NIL;
  FOR i := 0 TO a.AtomCount-1 DO
    IF a.USAGE(SYSTEM.VAL(a.Atom, SYSTEM.ADR(a.Memory[i]))) = a.Unreferenced THEN
      a.Memory[i].next := SYSTEM.VAL(a.Cell, a.Free);
      a.Memory[i].data := 0;
      a.Free := SYSTEM.VAL(a.Atom, SYSTEM.ADR(a.Memory[i]));
    END
  END
END RecycleUnusedAtoms;


PROCEDURE Collect*;
VAR i: a.Cell; link: a.Cell;
BEGIN
  (* Initialise all workspace atom usage counts to zero *)
  FOR i := 0 TO a.AtomCount-1 DO a.SETUSAGE(a.ATOM(SYSTEM.ADR(a.Memory[i])), 0) END;

  (* Register all lists beginning at intrinisic variables. *)
  FOR i := 0 TO 25 DO
    IF a.IntrinsicVariable[i] # 0 THEN
      RegisterListUsage(a.ATOM(a.IntrinsicVariable[i]))
    END
  END;

  (* Stack all lists *)
  FOR i := 0 TO 25 DO
    IF a.IntrinsicVariable[i] # 0 THEN
      StackList(a.ATOM(a.IntrinsicVariable[i]))
    END
  END;

  RecycleUnusedAtoms

END Collect;


END reorganise.

