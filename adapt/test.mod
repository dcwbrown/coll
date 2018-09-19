MODULE test;

IMPORT w, a, bootstrap, interpreter, dumping, SYSTEM;



PROCEDURE TestMakeFlatValue(t, addr: a.Address; verbose: BOOLEAN);
VAR buf: a.Block; i: a.Address; v: a.Value;
    dummy: a.AtomHeader;
BEGIN
  IF verbose THEN w.x(addr,16) END;
  buf.in := 0;
  IF a.CompressValue(t, addr, buf) THEN END;
  IF verbose THEN w.s(" flattened: "); dumping.whexbytes(buf.bytes, buf.in) END;

  v.header := a.ATOMPTR(SYSTEM.ADR(dummy));
  dummy.data := SYSTEM.ADR(buf.bytes) + buf.in;
  a.ExpandValue(SYSTEM.ADR(buf.bytes), v);

  IF verbose THEN
    w.s(", decoded: type "); w.x(v.kind,1); w.s(" data "); w.x(v.data,16); w.l
  END;
  w.Assert(t=v.kind,   "Flat value type lost.");
  w.Assert(addr=v.data,   "Flat value data lost.");
  w.Assert(v.next = 0, "More bytes encoded than decoded.");
END TestMakeFlatValue;

PROCEDURE TestFlattening;
VAR addr: a.Address;
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

  FOR addr := 0 TO 5000000 DO TestMakeFlatValue(0, addr, FALSE) END;
  FOR addr := 0 TO 5000000 DO TestMakeFlatValue(0, -addr, FALSE) END;

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



BEGIN
  w.sl("Adapt (Algorithms, Data And Prefix Trees) - test harness.");

  w.Assert(SYSTEM.VAL(a.Address, NIL) = 0, "Expected NIL to be zero.");
  w.s("Address size is "); w.i(SIZE(a.Address)*8); w.sl(" bits.");


  (* Load the bootstrap as intrinsic variable 'z'. *)
  a.IntrinsicVariable[25] := bootstrap.Load("test.boot");

  (* Run the bootstrap *)
  w.sl("Running bootstrap before regroup.");
  a.InitLink(interpreter.Program, a.IntrinsicVariable[25]);
  WHILE a.IsLink(interpreter.Program) DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.Arg);

  w.l; w.sl("All lists.");
  dumping.ListAll;

  (*
  RegroupAndCollect;

  w.l; w.sl("List of all lists after first RegroupAndCollect:");
  ListAll; w.l;

  w.sl("Dump of Boot after first RegroupAndCollect:");
  wlink(IntrinsicVariable[25]);

  w.sl("Run bootstrap after first RegroupAndCollect.");
  InitLink(interpreter.Program, IntrinsicVariable[25]);
  WHILE IsLink(interpreter.Program) DO Step END;

  RegroupAndCollect;
  w.s("Usage after second RegroupAndCollect, "); ShowUsage;

  w.sl("Dump of Boot after second RegroupAndCollect:");
  wlink(IntrinsicVariable[25]);

  w.sl("Run bootstrap after second RegroupAndCollect.");
  InitLink(interpreter.Program, IntrinsicVariable[25]);
  WHILE IsLink(interpreter.Program) DO Step END;
  *)

END test.

