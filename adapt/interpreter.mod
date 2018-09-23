MODULE interpreter;  (* interpreter - data, algorithms and memory *)

IMPORT w, a, In, SYSTEM;

CONST
  StackDepth = 100;

TYPE
  ValueStack = RECORD
    stk: ARRAY StackDepth OF a.Value;
    top: INTEGER
  END;

VAR
  Arg*:     ValueStack;
  Return*:  ValueStack;
  Program*: a.Value;


PROCEDURE wvalue(v: a.Value);
VAR l: a.Value;
BEGIN
  IF ~a.IsLink(v) THEN
    w.u(v.data)
  ELSE
    WHILE a.IsLink(v) DO
      IF v.kind = a.Int THEN w.u(v.data)
      ELSE w.c('['); l := v; a.Fetch(l); wvalue(l); w.c(']') END;
      a.Next(v)
    END
  END
END wvalue;


PROCEDURE wlink*(link: a.Cell);
VAR v: a.Value;
BEGIN
  w.s("Link: "); w.x(link,1); w.sl(", value: ");
  a.InitLink(v, link); wvalue(v)
END wlink;


(* -------------------------------- Stacks -------------------------------- *)

PROCEDURE Dup(VAR stk: ValueStack);
BEGIN
  w.Assert(stk.top > 0, "Cannot dup empty stk.");
  w.Assert(stk.top < LEN(stk.stk), "Cannot up full stk.");
  stk.stk[stk.top] := stk.stk[stk.top-1];
  INC(stk.top)
END Dup;

PROCEDURE Swap(VAR stk: ValueStack);
VAR v: a.Value;
BEGIN
  w.Assert(stk.top > 1, "Swap requires at least two items on stk.");
  v := stk.stk[stk.top-2];
  stk.stk[stk.top-2] := stk.stk[stk.top-1];
  stk.stk[stk.top-1] := v
END Swap;

PROCEDURE Drop(VAR stk: ValueStack);
BEGIN
  w.Assert(stk.top > 0, "Cannot drop from empty stk.");
  DEC(stk.top)
END Drop;

PROCEDURE DumpStack*(VAR stk: ValueStack);
VAR i: INTEGER;
BEGIN
  (* Dump any remaining stack content *)
  IF stk.top = 0 THEN w.sl("stack empty.")
  ELSE w.sl("stack content:");
    w.Assert(stk.top >= 0, "Negative stack top index.");
    FOR i := 0 TO stk.top-1 DO
      w.s("  ["); w.i(i); w.s("] ");
      wvalue(stk.stk[stk.top-1-i]); w.l;
    END
  END
END DumpStack;


(* ----------------------------- Interpreter ------------------------------ *)

PROCEDURE BoolVal(b: BOOLEAN): a.Cell;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE Step*;
VAR n, r1, r2: a.Value;  c: CHAR;  i: a.Cell;
BEGIN
  w.Assert(a.IsLink(Program), "Step expects Program to be a link.");
  n := Program; a.Next(n);
  IF Program.kind = a.Int THEN
    (*
    IF Program.data > 32 THEN w.s("Intrinsic '"); w.u(Program.data); w.sl("'.") END;
    IF Program.data > 32 THEN w.u(Program.data); w.fl END;
    *)
    CASE CHR(Program.data) OF
    |' ', 0AX, 0DX: (* No op   *)

    (* Intrinsic global variables a..z and integer literals 0..F *)
    |'a'..'z':         w.Assert(Arg.top < StackDepth,
                              "intrinsic variable blocked because arg stack is full.");
                       i := Program.data - ORD('a');
                       IF a.IntrinsicVariable[i] = 0 THEN
                         a.IntrinsicVariable[i] := SYSTEM.VAL(a.Cell, a.NewAtom())
                       END;
                       a.InitLink(Arg.stk[Arg.top], a.IntrinsicVariable[i]); INC(Arg.top)
                       (*w.s("Following initrinsic variable push, "); DumpStack(Arg); w.l*)

    |'0'..'9':         w.Assert(Arg.top < StackDepth,
                              "Intrinsic literal blocked because arg stack is full.");
                       INC(Arg.top); a.InitInt(Arg.stk[Arg.top-1], Program.data - ORD('0'))

    |'A'..'F':         w.Assert(Arg.top < StackDepth,
                              "Intrinsic literal blocked because arg stack is full.");
                       INC(Arg.top); a.InitInt(Arg.stk[Arg.top-1], Program.data - ORD('A') + 10)

    |'`':              w.Assert(Arg.top < StackDepth,
                              "'`' literal blocked because arg stack is full.");
                       w.Assert(n.kind = a.Int, "'`' expected a.Int.");
                       INC(Arg.top); a.InitInt(Arg.stk[Arg.top-1], n.data);
                       a.Next(n)

    (* Stack manipulation *)
    |'"':(* Dup     *) Dup(Arg);
    |'%':(* Swap    *) Swap(Arg);
    |'#':(* Drop    *) Drop(Arg);

    (* Basic operations *)
    |'~':(* Not     *) w.Assert(Arg.top >= 1, "'~' operator requires 1 arg.");
                       a.InitInt(Arg.stk[Arg.top-1], BoolVal(~a.Truth(Arg.stk[Arg.top-1])))

    |'=':(* Equal   *) w.Assert(Arg.top >= 2, "'=' operator requires 2 args.");
                       IF a.IsLink(Arg.stk[Arg.top-1]) # a.IsLink(Arg.stk[Arg.top-2]) THEN
                         a.InitInt(Arg.stk[Arg.top-2], 0)
                       ELSIF a.IsLink(Arg.stk[Arg.top-1]) THEN
                         a.InitInt(Arg.stk[Arg.top-2],
                                 BoolVal(Arg.stk[Arg.top-1].atom = Arg.stk[Arg.top-2].atom))
                       ELSE
                         a.InitInt(Arg.stk[Arg.top-2],
                                 BoolVal(Arg.stk[Arg.top-1].data = Arg.stk[Arg.top-2].data))
                       END;
                       DEC(Arg.top)

    |'+':(* Plus    *) w.Assert(Arg.top >= 2, "'+' operator requires 2 args.");
                       w.Assert(~a.IsLink(Arg.stk[Arg.top-1]), "'+' requires 2nd arg to be integer.");
                       w.Assert(~a.IsLink(Arg.stk[Arg.top-2]), "'+' requires 1st arg to be integer.");
                       a.InitInt(Arg.stk[Arg.top-2], Arg.stk[Arg.top-2].data + Arg.stk[Arg.top-1].data);
                       DEC(Arg.top)

    |'-':(* Minus   *) w.Assert(Arg.top >= 2, "'-' operator requires 2 args.");
                       w.Assert(~a.IsLink(Arg.stk[Arg.top-1]), "'-' requires 2nd arg to be integer.");
                       w.Assert(~a.IsLink(Arg.stk[Arg.top-2]), "'-' requires 1st arg to be integer.");
                       a.InitInt(Arg.stk[Arg.top-2], Arg.stk[Arg.top-2].data - Arg.stk[Arg.top-1].data);
                       DEC(Arg.top)

    |'&':(* And     *) w.Assert(Arg.top >= 2, "'&' operator requires 2 args.");
                       a.InitInt(Arg.stk[Arg.top-2],
                               BoolVal(a.Truth(Arg.stk[Arg.top-2]) & a.Truth(Arg.stk[Arg.top-1])));
                       DEC(Arg.top)

    (* Conditional *)
    |'?':(* If      *) w.Assert(Arg.top >= 2, "'?' operator requires 2 args.");
                       w.Assert(a.IsLink(Arg.stk[Arg.top-1]), "'?' requires link on TOS.");
                       IF a.Truth(Arg.stk[Arg.top-2]) THEN n := Arg.stk[Arg.top-1] END;
                       DEC(Arg.top, 2)

    |'@':(* Start   *) w.Assert(Arg.top < StackDepth, "'@' blocked because arg stack is full.");
                       w.Assert(Return.top > 0, "'@' reqires at least one entry on return stack.");
                       INC(Arg.top);
                       Arg.stk[Arg.top-1] := Return.stk[Return.top-1]

    (* Atom access *)
    |'_':(* a.IsLink  *) w.Assert(Arg.top >= 1, "'_' operator requires 1 arg.");
                       a.InitInt(Arg.stk[Arg.top-1], BoolVal(a.IsLink(Arg.stk[Arg.top-1])))

    |',':(* Next    *) w.Assert(Arg.top > 0, "Next requires an item on the stk.");
                       a.Next(Arg.stk[Arg.top-1])

    |'.':(* a.Fetch   *) w.Assert(Arg.top > 0, "a.Fetch requires an item on the stk.");
                       a.Fetch(Arg.stk[Arg.top-1])

    |':':(* Store   *) w.Assert(Arg.top >= 2, "':' store operator requires 2 args.");
                       w.Assert(a.IsLink(Arg.stk[Arg.top-1]), "Store requires link at top of stack.");
                       a.StoreValue(Arg.stk[Arg.top-2], Arg.stk[Arg.top-1]);
                       DEC(Arg.top, 2);

    (* Control transfer *)
    |'!':(* Execute *) w.Assert(Return.top < StackDepth-1,
                              "Cannot enter nested list as return stack is full.");
                       w.Assert(Arg.top >= 1, "'!' execute operator requires 1 arg.");
                       INC(Return.top); Return.stk[Return.top-1] := n;
                       n := Arg.stk[Arg.top-1];  DEC(Arg.top);
                       w.Assert(a.IsLink(n), "'!' execute expects Link.");
                       INC(Return.top); Return.stk[Return.top-1] := n;

    (* Input and output *)
    |'R':(* Input   *) w.Assert(Arg.top < StackDepth, "'R' read blocked because arg stack is full.");
                       In.Char(c);  INC(Arg.top);  a.InitInt(Arg.stk[Arg.top-1], ORD(c))

    |'W':(* Output  *) w.Assert(Arg.top >= 1, "W operator requires 1 arg.");
                       wvalue(Arg.stk[Arg.top-1]); DEC(Arg.top); w.fl

    |'L':(* Newline *) w.l

    |'S':(* DumpStk *) DumpStack(Arg)

    |'X':(* DbgExit *) w.Fail("'X' intrinsic - Forced debug exit.")

    ELSE w.lc; w.s("Unrecognised intrinsic code: ");
      w.i(Program.data); w.c(' '); w.u(Program.data); w.Fail("")
    END
  ELSE  (* handle program link - i.e.push linked list *)
    w.Assert(Arg.top < StackDepth, "Push link blocked because arg stack is full.");
    a.Fetch(Program);  INC(Arg.top);  Arg.stk[Arg.top-1] := Program
  END;
  Program := n;
  (* When Program is not a link we've reached end of function and must return to caller *)
  WHILE (~a.IsLink(Program)) & (Return.top > 1) DO
    DEC(Return.top);  Program := Return.stk[Return.top-1];  DEC(Return.top);
  END
END Step;


END interpreter.

