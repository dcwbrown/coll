MODULE test;

IMPORT w, a, bootstrap, interpreter, dumping, reorganise, SYSTEM;



PROCEDURE TestMakeFlatValue(data: a.Cell; verbose: BOOLEAN);
VAR buf: reorganise.Block; tested, addr: a.Cell;
BEGIN  NEW(buf);
  IF verbose THEN w.x(data,16) END;
  buf.in := 0;
  IF reorganise.Compress(data, buf) THEN END;
  IF verbose THEN w.s(" flattened: "); dumping.whexbytes(buf.bytes, buf.in) END;

  addr := SYSTEM.ADR(buf.bytes);
  a.Expand(addr, tested);

  IF verbose THEN
    w.s(", decoded: "); w.x(tested,16); w.l
  END;
  w.Assert(data=tested,   "Flat value data lost.");
  w.Assert(addr - SYSTEM.ADR(buf.bytes) = buf.in, "Byte count encoded # that decoded.");
END TestMakeFlatValue;


PROCEDURE TestFlattening;
VAR addr: a.Cell;
BEGIN
  TestMakeFlatValue(0000H, TRUE);
  TestMakeFlatValue(0001H, TRUE);
  TestMakeFlatValue(0002H, TRUE);
  TestMakeFlatValue(007FH, TRUE);
  TestMakeFlatValue(0080H, TRUE);
  TestMakeFlatValue(00FFH, TRUE);
  TestMakeFlatValue(0100H, TRUE);
  TestMakeFlatValue(01FFH, TRUE);
  TestMakeFlatValue(0200H, TRUE);
  TestMakeFlatValue(03FFH, TRUE);
  TestMakeFlatValue(0400H, TRUE);
  TestMakeFlatValue(07FFH, TRUE);
  TestMakeFlatValue(0800H, TRUE);
  TestMakeFlatValue(0FFFH, TRUE);
  TestMakeFlatValue(1000H, TRUE);
  TestMakeFlatValue(1FFFH, TRUE);
  TestMakeFlatValue(2000H, TRUE);
  TestMakeFlatValue(3FFFH, TRUE);
  TestMakeFlatValue(4000H, TRUE);
  TestMakeFlatValue(7FFFH, TRUE);
  TestMakeFlatValue(8000H, TRUE);

  TestMakeFlatValue(-0001H, TRUE);
  TestMakeFlatValue(-0002H, TRUE);
  TestMakeFlatValue(-0003H, TRUE);
  TestMakeFlatValue(-0080H, TRUE);
  TestMakeFlatValue(-0081H, TRUE);
  TestMakeFlatValue(-0100H, TRUE);
  TestMakeFlatValue(-0101H, TRUE);
  TestMakeFlatValue(-0200H, TRUE);
  TestMakeFlatValue(-0201H, TRUE);
  TestMakeFlatValue(-0400H, TRUE);
  TestMakeFlatValue(-0401H, TRUE);
  TestMakeFlatValue(-0800H, TRUE);
  TestMakeFlatValue(-0801H, TRUE);
  TestMakeFlatValue(-1000H, TRUE);
  TestMakeFlatValue(-1001H, TRUE);
  TestMakeFlatValue(-2000H, TRUE);
  TestMakeFlatValue(-2001H, TRUE);
  TestMakeFlatValue(-4000H, TRUE);
  TestMakeFlatValue(-4001H, TRUE);
  TestMakeFlatValue(-8000H, TRUE);
  TestMakeFlatValue(-8001H, TRUE);

  FOR addr := 0 TO 5000000 DO TestMakeFlatValue(addr, FALSE) END;
  FOR addr := 0 TO 5000000 DO TestMakeFlatValue(-addr, FALSE) END;

  TestMakeFlatValue(01FFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(01FFFFFFFFFFFFFFFH, TRUE);
  TestMakeFlatValue(02000000000000000H, TRUE);
  TestMakeFlatValue(02000000000000001H, TRUE);
  TestMakeFlatValue(07FFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(07FFFFFFFFFFFFFFFH, TRUE);
  TestMakeFlatValue(08000000000000000H, TRUE);
  TestMakeFlatValue(08000000000000001H, TRUE);
  TestMakeFlatValue(0DFFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(0DFFFFFFFFFFFFFFFH, TRUE);
  TestMakeFlatValue(0E000000000000000H, TRUE);
  TestMakeFlatValue(0E000000000000001H, TRUE);
  TestMakeFlatValue(0FFFFFFFFFFFFFFFEH, TRUE);
  TestMakeFlatValue(0FFFFFFFFFFFFFFFFH, TRUE);
END TestFlattening;


BEGIN
  w.sl("Adapt (Algorithms, Data And Prefix Trees) - test harness.");

  (*TestFlattening;*)

  w.Assert(SYSTEM.VAL(a.Cell, NIL) = 0, "Expected NIL to be zero.");
  w.s("Address size is "); w.i(SIZE(a.Cell)*8); w.sl(" bits.");


  (* Load the bootstrap as intrinsic variable 'z'. *)
  a.IntrinsicVariable[25] := bootstrap.Load("test.boot");

  w.sl("Dump of Boot as loaded:");
  interpreter.wlink(a.IntrinsicVariable[25]);

  (* Run the bootstrap *)
  w.sl("Running bootstrap before Collect.");
  a.InitLink(interpreter.Program, a.IntrinsicVariable[25]);
  WHILE a.IsLink(interpreter.Program) DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.Arg);

  w.l; w.sl("All lists before Collect.");
  dumping.ListAll;

  reorganise.Collect;

  w.sl("Dump of Boot after Collect:");
  interpreter.wlink(a.IntrinsicVariable[25]);

  w.l; w.sl("All lists after Collect.");
  dumping.ListAll;

  w.sl("Running bootstrap after Collect.");
  a.InitLink(interpreter.Program, a.IntrinsicVariable[25]);
  WHILE a.IsLink(interpreter.Program) DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.Arg);

  reorganise.Collect;

  w.sl("Dump of Boot after second Collect:");
  interpreter.wlink(a.IntrinsicVariable[25]);

  w.l; w.sl("All lists after second Collect.");
  dumping.ListAll;

  w.sl("Running bootstrap after second Collect.");
  a.InitLink(interpreter.Program, a.IntrinsicVariable[25]);
  WHILE a.IsLink(interpreter.Program) DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.Arg);

END test.

