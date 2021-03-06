MODULE test;

IMPORT w, a, bootstrap, interpreter, dumping, reorganise, SYSTEM;


PROCEDURE DumpStats;
VAR
  block: reorganise.Block;  free: a.Atom;
  freeatomcount, blockcount, blockbytecount: a.Cell;
BEGIN
  (* Measure Atoms in Memory[] statistics *)
  freeatomcount := 0;  free := a.Free;
  WHILE free # NIL DO
    INC(freeatomcount);  free := a.ATOM(free.next)
  END;

  (* Measure block usage statistics. *)
  blockcount := 0;  blockbytecount := 0;  block := reorganise.Blocks;
  WHILE block # NIL DO
    INC(blockcount);  INC(blockbytecount, block.in);
    block := block.next
  END;

  w.i((a.AtomCount - freeatomcount) * SIZE(a.AtomDesc)); w.s(" bytes in ");
  w.i(a.AtomCount - freeatomcount); w.sl(" atoms.");

  w.i(blockbytecount); w.s(" bytes in ");
  w.i(blockcount); w.sl(" blocks.");

  w.i((a.AtomCount - freeatomcount) * SIZE(a.AtomDesc) + blockbytecount); w.sl(" total.");
END DumpStats;


PROCEDURE DumpTree*(link: a.Cell);
VAR data, next: a.Cell;
BEGIN
  WHILE a.ADDR(link) # 0 DO
    a.FetchAtom(link, data, next);
    IF next MOD 4 = a.Int THEN
      IF (data < 32 ) & (data # 13) & (data # 10) THEN
        w.c('^'); w.i(data); w.c(' ')
      ELSE
        CASE data OF ORD('['), ORD(']'), ORD('^'): w.c('^') ELSE END;
        w.u(data)
      END
    ELSIF next MOD 4 = a.Link THEN
      w.c('['); DumpTree(data); w.c(']')
    ELSE
      w.Fail("Unexpected atom kind in DumpTree")
    END;
    link := next
  END;
END DumpTree;


BEGIN
  w.sl("Adapt (Algorithms, Data And a Prefix Tree) - test harness.");

  w.Assert(SYSTEM.VAL(a.Cell, NIL) = 0, "Expected NIL to be zero.");
  w.s("Address size is "); w.i(SIZE(a.Cell)*8); w.sl(" bits.");

  (* w.sl("Usage at start:"); DumpStats; *)

  (* Load the bootstrap as intrinsic variable 'z'. *)
  (*a.IntrinsicVariable[25] := bootstrap.Load("test.boot");*)
  a.IntrinsicVariable[25] := bootstrap.Load("match.boot");

  (*w.l; w.sl("Usage after bootstrap load:"); DumpStats;*)

  (* Run the bootstrap *)
  w.sl("Running bootstrap before first collection.");
  interpreter.ProgramLink := a.IntrinsicVariable[25];
  WHILE a.ADDR(interpreter.ProgramLink) # 0 DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.ArgStack);

  w.l; w.sl("Usage after bootstrap executed:"); DumpStats;

  w.l; w.sl("Final value of Z:"); DumpTree(a.IntrinsicVariable[25]); w.l;

  (*
  reorganise.Collect;

  ( *w.l; w.sl("Usage after first collection:"); DumpStats;* )

  ( * Run the bootstrap * )
  w.sl("Running bootstrap after first collection.");
  interpreter.ProgramLink := a.IntrinsicVariable[25];
  WHILE a.ADDR(interpreter.ProgramLink) # 0 DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.ArgStack);

  w.l; w.sl("Usage after bootstrap executed:"); DumpStats;

  reorganise.Collect;

  w.l; w.sl("Usage after second collection:"); DumpStats;

  w.sl("Running bootstrap after Collect.");
  a.InitLink(interpreter.Program, a.IntrinsicVariable[25]);
  WHILE a.IsLink(interpreter.Program) DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.Arg);

  w.l; w.sl("Usage after second bootstrap run:"); DumpStats;

  reorganise.Collect;

  w.l; w.sl("Usage after third collection:"); DumpStats;

  w.sl("Running bootstrap after second Collect.");
  a.InitLink(interpreter.Program, a.IntrinsicVariable[25]);
  WHILE a.IsLink(interpreter.Program) DO interpreter.Step END;
  w.lc; w.s("Bootstrap complete, ");
  interpreter.DumpStack(interpreter.Arg);

  w.l; w.sl("Usage after third bootstrap run:"); DumpStats;
  *)

END test.

