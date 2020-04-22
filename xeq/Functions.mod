MODULE Functions;  IMPORT w, Codespace, Codegen, SYSTEM;

CONST
     (* Dyadic operations *)
     AddOp = Codegen.AddOp;  OrOp  = Codegen.OrOp;
     AdcOp = Codegen.AdcOp;  SbbOp = Codegen.SbbOp;
     AndOp = Codegen.AndOp;  SubOp = Codegen.SubOp;
     XorOp = Codegen.XorOp;  CmpOp = Codegen.CmpOp;

     (* Dyadic direction *)
     From = Codegen.From;  To = Codegen.To;

     (* Dyadic operand form *)
     Register        = Codegen.Register;        AtAddress     = Codegen.AtAddress;
     AtCodeOffset    = Codegen.AtCodeOffset;    AtScaledIndex = Codegen.AtScaledIndex;
     AtBasePlusIndex = Codegen.AtBasePlusIndex;

     (* Dyadic index scale factors *)
     Scale0 = Codegen.Scale0;  Scale1 = Codegen.Scale1;  Scale2 = Codegen.Scale2;
     Scale4 = Codegen.Scale4;  Scale8 = Codegen.Scale8;


TYPE
  i8  = SYSTEM.INT8;
  i16 = SYSTEM.INT16;
  i32 = SYSTEM.INT32;
  i64 = SYSTEM.INT64;

  Fn = POINTER TO FnRec;
  FnRec = RECORD END;

  Constant = POINTER TO ConstantRec;
  ConstantRec = RECORD (FnRec) v: i64 END;

  Monadic = POINTER TO MonadicRec;
  MonadicRec = RECORD (FnRec) p: Fn END;

  Dyadic = POINTER TO DyadicRec;
  DyadicRec = RECORD (FnRec) p1, p2: Fn END;

  Add = POINTER TO AddRec;
  AddRec = RECORD (DyadicRec) END;

  Iterator = POINTER TO IteratorRec;
  IteratorRec = RECORD (FnRec) i: Dyadic END;

  ResultRec = RECORD
    form, value: i64;
  END;

  Function = POINTER TO FunctionRec;
  Handler = PROCEDURE(request: i64; VAR fn: Function; VAR result: ResultRec);
  FunctionRec = RECORD
    handle:         Handler;
    form, value:    i64;
    next, content:  Function;
  END;


  PROCEDURE (f: Fn) Value(): i64; BEGIN w.Fail("Abstract Value called.") END Value;
  PROCEDURE (f: Fn) Form():  i64; BEGIN w.Fail("Abstract Form called.")  END Form;
  PROCEDURE (f: Fn) Enter(): Fn;  BEGIN w.Fail("Abstract Enter called.") END Enter;
  PROCEDURE (f: Fn) Next():  Fn;  BEGIN w.Fail("Abstract Next called.")  END Next;
  PROCEDURE (f: Fn) Print;        BEGIN w.Fail("Abstract Print called.") END Print;

  PROCEDURE (f: Fn) Iterated(): BOOLEAN; BEGIN RETURN FALSE END Iterated;

  PROCEDURE (f: Constant) Value(): i64; BEGIN RETURN f.v END Value;
  PROCEDURE (f: Add) Value(): i64; BEGIN RETURN f.p1.Value() + f.p2.Value() END Value;

  PROCEDURE (f: Iterator) Iterated(): BOOLEAN; BEGIN RETURN TRUE END Iterated;

PROCEDURE Print(f: Fn);
BEGIN
  IF f.Iterated() THEN
    (* ???? *)
  ELSE
    w.i(f.Value())
  END
END Print;

PROCEDURE Test*;
VAR
  c1, c2: Constant;  add: Add;
BEGIN
  NEW(c1);  c1.v := 1;
  NEW(c2);  c2.v := 2;
  NEW(add); add.p1 := c1; add.p2 := c2;

  w.s("Interpreted result: "); Print(add); w.sl(".");
END Test;

END Functions.


(* Out of order ...


VAR
  RegistersInUse: SET;


PROCEDURE AllocateRegister(desired: i16): i16;
VAR r: i16;
BEGIN
  IF (desired >= 0) & ~(desired IN RegistersInUse) THEN
    r := desired
  ELSE r := 0;
    WHILE (r < 16) & (r IN RegistersInUse) DO INC(r) END;
  END;
  IF r < 16 THEN
    INCL(RegistersInUse, r);
    RETURN r
  ELSE
    w.Fail("Ran out of registers.")
  END;
END AllocateRegister;

PROCEDURE FreeRegister*(r: i16); BEGIN EXCL(RegistersInUse, r) END FreeRegister;
PROCEDURE FreeAll*; BEGIN RegistersInUse := {4,5} END FreeAll;  (* sp, bp are always in use *)



PROCEDURE Compile(f: Function; reg: i16): i16;  (* reg requests result register, returns actual register *)
VAR r1, r2: i16;  (* Registers *)
BEGIN
  CASE f.form OF
  | IntegerConstant:
    r1 := AllocateRegister(reg);
    Codegen.LoadConst(r1, 3, f.operation);
    RETURN r1;

  | IntegerInstruction:
    CASE f.operation OF
    |  Add:
       w.Assert(f.params # NIL, "Compile passed add function with no parameters.");
       w.Assert(f.params.next # NIL, "Compile passed add function with only one parameter.");
       w.Assert(f.params.next.next = NIL, "Compile passed add function with more than two parameters.");
       r1 := Compile(f.params, reg);
       r2 := Compile(f.params.next, -1);
       Codegen.Dyadic(AddOp, 3, r1, From, Register, r2, Scale0, 0, 0);
       FreeRegister(r2);
       RETURN r1

    ELSE w.Fail("Compile passed function with unrecognised integer instruction.")
    END;

  ELSE w.Fail("Compile passed unrecognised form of function.")
  END
END Compile;


PROCEDURE Test*;
VAR
  f1, f2, f3, f4: Function;
  r: i16;
  entry: Codespace.Entry;
BEGIN
  MakeFunction(f1, IntegerConstant, 2);
  MakeFunction(f2, IntegerConstant, 3);
  MakeFunction(f3, IntegerInstruction, Add);
  f1.next := f2;
  f3.params := f1;

  w.s("Interpreted result: "); Print(f3); w.l;


  FreeAll;
  Codespace.Origin(0); Codespace.Bss(32); Codespace.Origin(0);
  entry := Codespace.GetEntry();
  r := Compile(f3, 0);
  IF r # 0 THEN Codegen.CopyReg(0, r, 3) END;
  Codegen.Ret;

  Codespace.Dump(0, Codespace.GetOffset());

  w.s("Called code result rax = "); w.x(entry(), 16); w.nb; w.sl("H.");


END Test;

BEGIN
  RegistersInUse := {};
END Functions.

