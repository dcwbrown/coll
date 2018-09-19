MODULE bootstrap;

IMPORT Files, w, a, SYSTEM;

VAR
  BootState:  INTEGER;  (* 0 - normal, 1 - escaped, 2 - number *)
  BootNumber: INTEGER;
  BootStack:  ARRAY 10 OF a.AtomPtr;
  BootTop:    INTEGER;


PROCEDURE AddAtom(VAR current: a.AtomPtr; data: a.Address);
BEGIN
  a.SETPTR(current.next, a.NewAtom());
  current := a.ATOMPTR(current.next);
  current.data := data
END AddAtom;

PROCEDURE AddChar(VAR current: a.AtomPtr;  ch: CHAR);
VAR link: a.AtomPtr;
BEGIN
  IF (BootState = 2) & ((ch < '0') OR (ch > '9')) THEN
    AddAtom(current, BootNumber);
    BootState := 0;
  END;
  CASE BootState OF
  |0: CASE ch OF
      |'^': BootState := 1;
      |'[': AddAtom(current, 0);  BootStack[BootTop] := current;  INC(BootTop);
      |']': DEC(BootTop);  link := BootStack[BootTop];
            link.data := a.LINK(link.next);
            link.next := a.Link;
            w.Assert(a.LINK(current.next) = 0, "Expected current.next to be at end of list in ']'.");
            current := link;
            link := a.ATOMPTR(link.data);
      ELSE  AddAtom(current, ORD(ch))
      END
  |1: IF (ch >= '0') & (ch <= '9') THEN
        BootNumber := ORD(ch) - ORD('0');
        w.s("Boot escaped number. First digit "); w.i(BootNumber); w.l;
        BootState := 2;
      ELSE
        AddAtom(current, ORD(ch));
        BootState := 0
      END
  |2: BootNumber := BootNumber*10 + ORD(ch) - ORD('0')
  ELSE w.Fail("Invalid boot state.")
  END
END AddChar;


PROCEDURE Load*(fn: ARRAY OF CHAR): a.Address;
VAR head, current, nest: a.AtomPtr;
    i:                   INTEGER;
    f:                   Files.File;
    r:                   Files.Rider;
    c:                   CHAR;
BEGIN BootTop := 0;
  head := a.NewAtom();  current := head;  BootState := 0;
  f := Files.Old(fn);  w.Assert(f # NIL, "Expected file bootstrap.boot.");
  Files.Set(r, f, 0);  Files.Read(r, c);
  WHILE ~r.eof DO
    IF c # 0DX THEN AddChar(current, c) END;
    Files.Read(r, c)
  END;
RETURN head.next END Load;


END bootstrap.

