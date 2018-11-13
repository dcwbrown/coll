MODULE interpreter;  (* interpreter - data, algorithms and memory *)

IMPORT w, a, In, SYSTEM;


CONST
  StackDepth = 100;


VAR
  ProgramLink*:  a.Cell;  (* Currently executing program *)
  ArgStack*:     a.Cell;  (* Argument stack *)
  ReturnStack*:  a.Cell;  (* Function return stack *)
  LocalStack*:   a.Cell;  (* Local variables stack *)
  Locals:        a.Cell;  (* Current local variables *)


PROCEDURE wList*(link: a.Cell);
VAR data, next: a.Cell;
BEGIN
  WHILE a.ADDR(link) # 0 DO
    a.FetchAtom(link, data, next);
    IF next MOD 4 = a.Int THEN
      w.u(data)
    ELSE
      (*w.c('['); wList(data); w.c(']')*)
      (*w.u(02770H); wList(data); w.u(02771H)*)
      (*w.u(2039H); wList(data); w.u(203AH)*)
      w.u(169CH); wList(data); w.u(169BH)
    END;
    link := next
  END;
END wList;


PROCEDURE wValue*(atom: a.Atom);
BEGIN
  w.Assert(a.KIND(atom) < a.Flat, "wValue unexpectedly passed flat atom.");
  IF a.KIND(atom) = a.Int THEN
    w.u(atom.data)
  ELSE
    wList(atom.data)
  END
END wValue;


PROCEDURE wKind*(cell: a.Cell);
BEGIN
  CASE cell MOD 4 OF
  |a.Int:  w.s("Int")
  |a.Link: w.s("Link")
  |a.Flat: w.s("Flat")
  ELSE     w.s("invalid<"); w.x(cell,1); w.c('>')
  END
END wKind;


(* -------------------------------- Stacks -------------------------------- *)

PROCEDURE Dup*(VAR stack: a.Cell);
VAR atom: a.Atom;
BEGIN
  w.Assert(a.KIND(a.ATOM(stack)) < a.Flat, "Dup of flat atom not allowed.");
  atom := a.NewAtom();
  atom.next := stack;
  a.FetchValue(stack, atom);
  stack := SYSTEM.VAL(a.Cell, atom)
END Dup;


PROCEDURE Swap*(VAR stack: a.Cell);
VAR a1, a2: a.Atom;
BEGIN
  a1 := a.ATOM(stack);
  w.Assert(a.KIND(a1) < a.Flat, "Swap of flat atom not allowed.");
  w.Assert(a.ATOM(a1.next) # NIL, "Swap requires at least two items on stack.");
  a2 := a.ATOM(a2.next);
  w.Assert(a.KIND(a2) < a.Flat, "Swap of flat atom not allowed.");
  a.SETLINK(a1.next, a.LINK(a2.next));
  a.SETLINK(a2.next, SYSTEM.VAL(a.Cell, a1));
  stack := SYSTEM.VAL(a.Cell, a2)
END Swap;

PROCEDURE Drop*(VAR stack: a.Cell);
VAR atom: a.Atom;
BEGIN
  atom := a.ATOM(stack);
  w.Assert(atom # NIL, "Drop called with empty stack.");
  w.Assert(a.KIND(atom) < a.Flat, "Drop of flat atom not allowed.");
  stack := a.LINK(atom.next);
  a.SETLINK(SYSTEM.VAL(a.Cell, atom), 0)
END Drop;

PROCEDURE DumpStack*(stack: a.Cell);
VAR i: INTEGER;  data, next: a.Cell;
BEGIN
  IF a.ADDR(stack) = 0 THEN w.sl("stack empty.")
  ELSE
    i := 0;
    w.sl("stack content:");
    WHILE a.ADDR(stack) # 0 DO
      w.lc; w.s("  ["); w.i(i); w.s("] ");
      a.FetchAtom(stack, data, next);
      IF next MOD 4 >= a.Flat THEN
        w.sl(" kind > 1 (not dumping content).");
      ELSIF next MOD 4 = a.Int THEN
        w.s(" Int:  "); w.i(data); w.s(", '"); w.u(data); w.sl("'.")
      ELSE
        w.s(" Link: "); wList(data)
      END;
      INC(i);
      stack := a.LINK(next)
    END
  END
END DumpStack;

PROCEDURE PushData(VAR stack: a.Cell; data: a.Cell);
VAR top: a.Atom;
BEGIN
  top := a.NewAtom();  top.data := data;
  a.SETLINK(top.next, stack);  stack := SYSTEM.VAL(a.Cell, top)
END PushData;

PROCEDURE PushLink(VAR stack: a.Cell; link: a.Cell);
BEGIN
  PushData(stack, link);  a.SETKIND(a.ATOM(stack), a.Link)
END PushLink;

PROCEDURE PushInt(VAR stack: a.Cell; int: a.Cell);
BEGIN
  PushData(stack, int);  a.SETKIND(a.ATOM(stack), a.Int)
END PushInt;

PROCEDURE Top1(stack: a.Cell; VAR atom: a.Atom; id: CHAR);
CONST debug = FALSE;
BEGIN
  atom := a.ATOM(stack);
  IF atom = NIL THEN w.lc; w.s("Assertion failure: '"); w.c(id);
                     w.sl("' operator requires 1 arg but stack empty.") END;

  IF debug THEN
    w.lc; w.s("Top1 stack link to "); w.x(stack, 1); w.l;
    w.s("  atom.next "); w.x(atom.next,16); w.l;
    w.s("  atom.data "); w.x(atom.data,16); w.l;
  END;

END Top1;

PROCEDURE Top2(stack: a.Cell; VAR a1, a2: a.Atom; id: CHAR);
CONST debug = FALSE;
BEGIN
  a2 := a.ATOM(stack);
  IF a2 = NIL THEN w.lc; w.s("Assertion failure: '"); w.c(id);
                   w.sl("' operator requires 2 args but stack empty.") END;
  a1 := a.ATOM(a2.next);
  IF a1 = NIL THEN w.lc; w.s("Assertion failure: '"); w.c(id);
                   w.sl("' operator requires 2 args but stack has only one.") END;

  IF debug THEN
    w.lc; w.s("Top2 stack link to "); w.x(stack, 1); w.l;
    w.s("  a1.next "); w.x(a1.next,16); w.l;
    w.s("  a1.data "); w.x(a1.data,16); w.l;
    w.s("  a2.next "); w.x(a2.next,16); w.l;
    w.s("  a2.data "); w.x(a2.data,16); w.l;
  END;

END Top2;


(* ----------------------------- Interpreter ------------------------------ *)

PROCEDURE BoolVal(b: BOOLEAN): a.Cell;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE Step*;
CONST debug = FALSE;
VAR
  data, next, nextdata, nextnext, i: a.Cell;
  c: CHAR;
  a1, a2, r: a.Atom;
BEGIN
  a.FetchAtom(ProgramLink, data, next);
  IF next MOD 4 = a.Int THEN

    IF debug THEN
      w.lc;
      IF data > 32 THEN w.s("Intrinsic '"); w.u(data); w.sl("'.") END;
      (*IF data > 32 THEN w.u(data); w.fl END;*)
    END;

    CASE CHR(data) OF
    |' ', 0AX, 0DX: (* No op   *)

    (* Integer literals 0..9 *)
    |'0'..'9':         PushInt(ArgStack, data - ORD('0'))

    (* Intrinsic global variables a..z *)
    |'a'..'z':         i := data - ORD('a');
                       w.Assert(a.IntrinsicVariable[i] # 0, "Cannot load undefined intrinsic variable.");
                       PushData(ArgStack, 0);
                       a.FetchValue(a.IntrinsicVariable[i], a.ATOM(ArgStack))

    |'`':(* ToVar   *) a.FetchAtom(next, nextdata, nextnext);
                       w.Assert((nextnext MOD 4 = a.Int)
                              & (nextdata >= ORD('a'))
                              & (nextdata <= ORD('z')), "'$' (Addr) expects local var name following.");
                       i := nextdata - ORD('a');
                       IF a.IntrinsicVariable[i] = 0 THEN
                         a.IntrinsicVariable[i] := SYSTEM.VAL(a.Cell, a.NewAtom())
                       END;
                       a.FetchValue(ArgStack, a.ATOM(a.IntrinsicVariable[i]));
                       Drop(ArgStack);
                       next := nextnext

    |"'":(* Literal *) a.FetchAtom(next, nextdata, nextnext);
                       w.Assert(nextnext MOD 4 = a.Int, "'`' expected a.Int.");
                       PushInt(ArgStack, nextdata);
                       next := nextnext

    (* Stack manipulation *)
    |'"':(* Dup     *) Dup(ArgStack);
    |'%':(* Swap    *) Swap(ArgStack);
    |'#':(* Drop    *) Drop(ArgStack);

    (* Basic operations *)
    |'~':(* Not     *) Top1(ArgStack, a1, CHR(data));
                       a1.data := BoolVal(a1.data = 0);
                       a.SETKIND(a1, a.Int);

    |'=':(* Equal   *) Top2(ArgStack, a1, a2, CHR(data));
                       IF a.KIND(a1) # a.KIND(a2) THEN
                         a1.data := 0
                       ELSE
                         a1.data := BoolVal(a1.data = a2.data)
                       END;
                       a.SETKIND(a1, a.Int);
                       Drop(ArgStack)

    |'<':(* Lessthn *) Top2(ArgStack, a1, a2, CHR(data));
                       w.Assert(a.KIND(a1) = a.Int, "'<' requires 1st arg to be integer.");
                       w.Assert(a.KIND(a2) = a.Int, "'<' requires 2nd arg to be integer.");
                       a1.data := BoolVal(a1.data < a2.data);
                       a.SETKIND(a1, a.Int);
                       Drop(ArgStack)

    |'+':(* Plus    *) Top2(ArgStack, a1, a2, CHR(data));
                       w.Assert(a.KIND(a1) = a.Int, "'+' requires 1st arg to be integer.");
                       w.Assert(a.KIND(a2) = a.Int, "'+' requires 2nd arg to be integer.");
                       a1.data := a1.data + a2.data;
                       Drop(ArgStack)

    |'-':(* Minus   *) Top2(ArgStack, a1, a2, CHR(data));
                       w.Assert(a.KIND(a1) = a.Int, "'-' requires 1st arg to be integer.");
                       w.Assert(a.KIND(a2) = a.Int, "'-' requires 2nd arg to be integer.");
                       a1.data := a1.data - a2.data;
                       Drop(ArgStack)

    |'&':(* And     *) Top2(ArgStack, a1, a2, CHR(data));
                       a1.data := BoolVal((a1.data # 0) & (a2.data # 0));
                       a.SETKIND(a1, a.Int);
                       Drop(ArgStack)

    |'|':(* Or      *) Top2(ArgStack, a1, a2, CHR(data));
                       a1.data := BoolVal((a1.data # 0) OR (a2.data # 0));
                       a.SETKIND(a1, a.Int);
                       Drop(ArgStack)

    (* Conditional *)
    |'?':(* If      *) Top2(ArgStack, a1, a2, CHR(data));
                       w.Assert(a.KIND(a2) = a.Link, "'?' requires link on TOS.");
                       IF a1.data # 0 THEN
                         next := a2.data;
                         r := a.ATOM(ReturnStack);
                         w.Assert(r # NIL, "'?' operator requires non-empty return stack.");
                         r.data := next;           (* maintain top of return stack as *)
                         a.SETKIND(r, a.Link)      (* start of currently executing list *)
                       END;
                       Drop(ArgStack); Drop(ArgStack)

    |'@':(* Start   *) r := a.ATOM(ReturnStack);
                       w.Assert(r # NIL, "'@' operator requires non-empty return stack.");
                       w.Assert(a.KIND(r) = a.Link, "'@' operator requires link on top of return stack");
                       PushLink(ArgStack, r.data)


    (* Atom access *)
    |'_':(* IsLink  *) Top1(ArgStack, a1, CHR(data));
                       a1.data := BoolVal(a.KIND(a1) = a.Link);
                       a.SETKIND(a1, a.Int);

    |',':(* Next    *) Top1(ArgStack, a1, CHR(data));
                       w.Assert(a.KIND(a1) = a.Link, "',' (next) expects link on top of stack.");
                       a.FetchAtom(a1.data, nextdata, nextnext);
                       IF a.ADDR(nextnext) = 0 THEN
                         a1.data := 0;
                         a.SETKIND(a1, a.Int)
                       ELSE
                         a1.data := nextnext
                       END;

    |'.':(* Fetch   *) Top1(ArgStack, a1, CHR(data));
                       w.Assert(a.KIND(a1) = a.Link, "'.' (fetch) requires a link on the stack.");
                       a.FetchValue(a1.data, a1)

    |':':(* Store   *) Top2(ArgStack, a1, a2, CHR(data));
                       w.Assert(a.KIND(a2) = a.Link, "Store requires a link on top of the stack.");
                       a2 := a.ATOM(a2.data);  (* Address target atom *)
                       w.Assert(a.KIND(a2) < a.Flat, "Store requires unflattened target atom.");
                       a2.data := a1.data;
                       a.SETKIND(a2, a.KIND(a1));
                       Drop(ArgStack); Drop(ArgStack)

    (* Local variables *)
    |'(':(* Locals  *) Top1(ArgStack, a1, CHR(data));
                       w.Assert(a.KIND(a1) = a.Int, "'(' (Locals) expects integer parameter.");
                       w.Assert(a1.data >= 0, "'(' (Locals) expects positive integer parameter.");
                       w.Assert(a1.data <= 8, "'(' (Locals) expects no more than 8 variables.");
                       PushLink(LocalStack, Locals);
                       i := a1.data - 1;
                       ArgStack := a.LINK(a1.next);
                       Locals := 0;
                       WHILE i >= 0 DO
                         a1 := a.ATOM(ArgStack);
                         w.Assert(a1 # NIL, "Insufficient stack items for '(' local definition.");
                         ArgStack := a.LINK(a1.next);
                         a.SETLINK(a1.next, Locals);
                         Locals := SYSTEM.VAL(a.Cell, a1);
                         a.IntrinsicVariable[i] := Locals;
                         DEC(i)
                       END;

    |')':(* Lexit   *) Top1(LocalStack, a1, CHR(data));  (* a1 is a link to the stack slice. *)
                       w.Assert(a.KIND(a1) = a.Link, "')' (Lexit) expects local stack to contain link.");
                       LocalStack := a.LINK(a1.next);
                       Locals := a.LINK(a1.data);
                       i := 0;
                       a1 := a.ATOM(Locals);
                       WHILE a1 # NIL DO
                         a.IntrinsicVariable[i] := SYSTEM.VAL(a.Cell, a1);
                         a1 := a.ATOM(a1.next);
                         INC(i)
                       END;

    (* Control transfer *)
    |'!':(* Execute *) Top1(ArgStack, a1, CHR(data));
                       w.Assert(a.KIND(a1) = a.Link, "'!' operator requires a link on top of stcak.");
                       PushLink(ReturnStack, next);
                       next := a1.data;
                       PushLink(ReturnStack, next);
                       Drop(ArgStack)

    (* Input and output *)
    |'R':(* Input   *) In.Char(c);  PushInt(ArgStack, ORD(c))

    |'W':(* Output  *) Top1(ArgStack, a1, CHR(data));
                       wValue(a1);
                       Drop(ArgStack)

    |'C':(* CondNL  *) w.lc
    |'L':(* Newline *) w.l

    |'S':(* DumpStk *) DumpStack(ArgStack)

    |'E':(* End     *) next := 0
    |'X':(* DbgExit *) w.Fail("'X' intrinsic - Forced debug exit.")

    ELSE w.lc; w.s("Unrecognised intrinsic code: ");
      w.i(data); w.c(' '); w.u(data); w.Fail("")
    END
  ELSE  (* handle program link - i.e.push linked list *)
    PushLink(ArgStack, data)
  END;
  ProgramLink := next;
  (* When Program is not a link we've reached end of function and must return to caller *)
  WHILE (a.ADDR(ProgramLink) = 0) & (a.ADDR(ReturnStack) # 0) DO
    Drop(ReturnStack);  (* Drop start of current function *)
    a.FetchAtom(ReturnStack, ProgramLink, next);
    w.Assert(next MOD 4 = a.Link, "Expected return link on return stack.");
    Drop(ReturnStack)
  END
END Step;


BEGIN
  ProgramLink := 0;
  ArgStack    := 0;
  ReturnStack := 0;
  LocalStack  := 0;
  Locals      := 0
END interpreter.

