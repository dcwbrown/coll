MODULE dumping;  (* dumping - data, algorithms and memory *)

IMPORT w, a, SYSTEM;

TYPE
  AtomList = POINTER TO AtomListDesc;  (* For ListAll debugging dump. *)
  AtomListDesc = RECORD
    atom: a.Address;
    next: AtomList;
  END;

VAR
  Lists: AtomList;  (* For ListAll debugging dump *)


(* --------------------------------- Values --------------------------------- *)

PROCEDURE^ DumpHeader(addr: a.Address);

PROCEDURE wkind(k: a.Address);
BEGIN CASE k OF
  |a.Int:  w.s("Int")
  |a.Link: w.s("Link")
  |a.Flat: w.s("Flat")
  ELSE     w.s("invalid<"); w.i(k); w.c('>')
  END
END wkind;

PROCEDURE DumpValue(v: a.Value);
VAR link: a.Address;
BEGIN
  w.s("DumpValue");
  w.s(". Header at ");   w.x(SYSTEM.VAL(a.Address, v.header), 16);
  IF v.header # NIL THEN
    w.s(" ("); w.x(v.header.next, 16); w.s(", "); w.x(v.header.data, 16); w.s(")");
    w.l;
    w.s("  header usage "); w.i(a.USAGE(v.header));
    w.s(", header kind ");  wkind(a.KIND(v.header));
  END;
  w.s(", current kind "); wkind(v.kind);
  w.s(", current data "); w.x(v.data, 1);
  IF v.pos # 0 THEN
    w.s(", pos ");  w.x(v.pos, 16);
    w.s(", next "); w.x(v.next, 16)
  END;
  w.l;
  IF a.KIND(v.header) = a.Flat THEN
    w.sl("Flat block ");
    link := SYSTEM.ADR(v.header.next);  a.SETPARAM(link, SIZE(a.AtomHeader));
    DumpHeader(link)
  END;
END DumpValue;


(* --------------------------- Regroup debugging ---------------------------- *)

PROCEDURE whexbytes*(buf: ARRAY OF a.Int8; len: a.Address);
VAR i: a.Address;
BEGIN
  FOR i := 0 TO len-1 DO
    w.x(buf[i],2);
    IF i < len-1 THEN w.c(" ") END
  END
END whexbytes;

PROCEDURE ShowUsage;
CONST rowlength = 100;
VAR i: INTEGER;
BEGIN
  w.sl("workspace atom usage:");
  i := 0; WHILE i < a.AtomCount DO
    IF i MOD rowlength = 0 THEN w.s("  ") END;
    w.c(CHR(a.USAGE(SYSTEM.VAL(a.AtomPtr, SYSTEM.ADR(a.Memory[i]))) + ORD('0')));
    INC(i);
    IF i MOD rowlength = 0 THEN w.l END
  END;
  IF i MOD rowlength # 0  THEN w.l END;
END ShowUsage;

PROCEDURE DumpHeader(addr: a.Address);
VAR hdr: a.AtomPtr; val: a.Value;
BEGIN
  hdr := a.ATOMPTR(addr);
  w.s("Header at ");  w.x(addr, 16); w.l;
  w.s("  next: ");    w.x(hdr.next,16);
  w.s(" (usage ");    w.i(a.USAGE(hdr));
  w.s(", kind ");     wkind(a.KIND(hdr)); w.sl(")");
  w.s("  data: ");    w.x(hdr.data,16);
  IF a.KIND(hdr) = a.Flat THEN
    w.s(" => length "); w.i(hdr.data - (a.PTR(addr) + SIZE(a.AtomHeader))); w.sl(" bytes.")
  END;
  a.CheckLink("DumpHeader", addr);
  a.InitLink(val, addr);
  w.s("  content: '");
  LOOP
    CASE val.kind OF
    |a.Int:  w.u(val.data)
    |a.Link: w.c("<"); w.x(val.data,1); w.c(">")
    ELSE     w.s("<bad kind "); w.i(val.kind); w.s(">")
    END;
    IF val.next = 0 THEN EXIT END;
    a.Next(val)
  END;
  w.sl("'.");
END DumpHeader;

PROCEDURE DumpBlock(block: a.BlockPtr);
CONST BytesPerLine = 32;
VAR i: a.Address; addr: a.Address; hdr: a.AtomPtr;
BEGIN
  w.s("Block at "); w.x(SYSTEM.VAL(a.Address, block),16); w.l;
  w.s("  in:   "); w.i(block.in); w.l;
  w.s("  next: "); w.x(SYSTEM.VAL(a.Address, block.next),16); w.l;

  (* Hex dump *)
  i := 0;
  WHILE i < block.in DO
    IF i MOD BytesPerLine = 0 THEN w.s("  "); w.x(i,4); w.s(": ") END;
    w.x(block.bytes[i],2); w.c(" ");
    IF i MOD BytesPerLine = BytesPerLine - 1 THEN w.l END;
    INC(i)
  END;
  IF i MOD BytesPerLine # 0 THEN w.l END;

  (* Interpreted dump *)
  i := 0; WHILE i < block.in DO
    addr := SYSTEM.ADR(block.bytes[i]);
    a.SETPARAM(addr, SIZE(a.AtomHeader));
    w.lc; DumpHeader(addr);
    hdr  := a.ATOMPTR(addr);
    i := hdr.data - SYSTEM.ADR(block.bytes);
    a.AlignUp(i, SIZE(a.AtomHeader));
  END;
END DumpBlock;


PROCEDURE DumpBlocks;
VAR block: a.BlockPtr;
BEGIN
  block := a.Blocks;
  WHILE block # NIL DO DumpBlock(block); block := block.next END
END DumpBlocks;

PROCEDURE CheckVariableUsages;
VAR i: INTEGER; v: a.Value;
BEGIN
  FOR i := 0 TO 25 DO
    IF a.IntrinsicVariable[i] # 0 THEN
      w.s("Intrinsic '"); w.u(ORD('a') + i); w.s("' ");
      a.InitLink(v, a.IntrinsicVariable[i]);
      DumpValue(v)
    END
  END
END CheckVariableUsages;



(* ---------------------- Formatted list of all atoms --------------------- *)

PROCEDURE AddList(l: a.Address);
VAR list: AtomList;  v: a.Value;
BEGIN
  IF l # 0 THEN
    list := Lists;  (* Check first whether this list is already recorded *)
    WHILE (list # NIL) & (list.atom # l) DO list := list.next END;

    IF list = NIL THEN
      (* List is not already recorded, add it. *)
      NEW(list);
      list.atom := l;

      a.InitLink(v, l);
      WHILE a.IsLink(v) DO
        IF v.kind = a.Link THEN AddList(v.data) END;
        a.Next(v)
      END;

      list.next := Lists;  Lists := list
    END
  END
END AddList;

PROCEDURE NameList(link: a.Address): CHAR;
VAR i: INTEGER;
BEGIN
  FOR i := 0 TO 25 DO
    IF a.IntrinsicVariable[i] = link THEN RETURN CHR(ORD('a') + i) END
  END;
  RETURN ' '
END NameList;

PROCEDURE ListList(link: a.Address);
VAR v: a.Value; inworkspace: BOOLEAN;
BEGIN inworkspace := TRUE;
  w.c(NameList(link)); w.c(" ");
  w.x(link,16); w.s(": ");
  a.InitLink(v, link);
  WHILE a.IsLink(v) DO
    IF (v.pos = 0) # inworkspace THEN
      IF v.pos # 0 THEN w.c('{') ELSE w.c('}') END;
      inworkspace := v.pos = 0;
    END;
    IF v.kind = a.Link THEN
      w.c("<"); w.x(v.data,1); w.c(">")
    ELSE
      CASE v.data OF
      |0AH: w.s("<l>")
      |0DH:
      |20H:
      ELSE w.u(v.data)
      END
    END;
    a.Next(v);
  END;
  IF ~inworkspace THEN w.c("}") END;
  w.l
END ListList;

PROCEDURE ListAll*;
VAR i: INTEGER; l: AtomList;
BEGIN
  Lists := NIL;
  FOR i := 0 TO 25 DO AddList(a.IntrinsicVariable[i]) END;
  l := Lists;
  WHILE l # NIL DO ListList(l.atom); l := l.next END
END ListAll;




END dumping.

