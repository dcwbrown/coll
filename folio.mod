MODULE folio;  (* folio - forthish lispish language with just nesting in the core *)

(*

    Basic text representation is one atom per node.

    Over time, static strings of atoms are re-represented as byte arrays.

    Atoms are 64 bit values that can be
      -  a character code (Unicode 21 bit valueA
      -  a numeric value (integer or floating point)
      -  a memory reference to an atom or AtriOg

    The interpretation of the 64 bits is entirely dependent on context. There
    are no flags in the atom itself to determine context.

 *)

IMPORT TextWriter, SYSTEM;

CONST
  (* Node types *)
  IntNode  = 1;
  LinkNode = 2;
  GenNode  = 3;
  (* Any other type is a fault in an allocated list. Free nodes use type 0 *)

  (* Intrinsic instructions *)
  CoreFault    = 0;
  CoreConstant = 1;
  CorePrint    = 2;
  CoreAdd      = 3;

TYPE
  i64 = SYSTEM.INT64;
  Node = POINTER [0] TO NodeDesc;
  NodeDesc = RECORD [0]
    prev: i64;
    next: i64;
    v1:   i64;
    v2:   i64;
  END;

VAR
   Abort: BOOLEAN;
   Stack: Node;
   Free:  Node;
   Store: Node;

(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)  END ws;
PROCEDURE wc(c: CHAR);           BEGIN TextWriter.Char(c)    END wc;
PROCEDURE wl;                    BEGIN TextWriter.NewLine    END wl;
PROCEDURE wi(i: LONGINT);        BEGIN TextWriter.Integer(i) END wi;
PROCEDURE wx(i,n: LONGINT);      BEGIN TextWriter.Hex(i,n)   END wx;
PROCEDURE wnb;                   BEGIN TextWriter.NoBreak    END wnb;
PROCEDURE wlc;                   BEGIN TextWriter.StartLine  END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl             END wsl;


(* ----------------- Error handling convenience functions ------------------- *)

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Internal error:"); wsl(msg); HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* ------------------------------- Dispensers ------------------------------- *)


PROCEDURE TypeOf(i: i64): i64;  BEGIN RETURN i MOD 16                    END TypeOf;
PROCEDURE AddrOf(i: i64): i64;  BEGIN RETURN i-TypeOf(i)                 END AddrOf;
PROCEDURE NodeOf(i: i64): Node; BEGIN RETURN SYSTEM.VAL(Node, AddrOf(i)) END NodeOf;

PROCEDURE DumpInt(i: i64);
BEGIN
  wi(i);
  IF (i >= 32) & (i < 127) THEN
    ws(" '"); wc(CHR(i)); wc("'")
  END
END DumpInt;

PROCEDURE DumpNode(n: Node);
VAR nodeaddr: i64;
BEGIN
  ws("Node at "); wx(SYSTEM.VAL(i64, n), 16); wsl(":");
  ws("  prev: "); wx(AddrOf(n.prev), 16); ws(", ");
  IF 0 IN SYSTEM.VAL(SET, n.prev) THEN ws("link from prev, ") ELSE ws("next of prev, ") END;
  IF 1 IN SYSTEM.VAL(SET, n.prev) THEN wsl("packed block.") ELSE wsl("node.") END;
  ws("  next: "); wx(AddrOf(n.next), 16); ws(", type "); wi(TypeOf(n.next));
  CASE TypeOf(n.next) OF
  | IntNode:  wsl(" - IntNode.")
  | LinkNode: wsl(" - LinkNode.")
  | GenNode:  wsl(" - GenNode.")
  ELSE        wsl(" - Faulty node.")
  END;
  ws("  v1:   "); DumpInt(n.v1); wsl(".");
  ws("  v2:   "); DumpInt(n.v2); wsl(".");
END DumpNode;


PROCEDURE MakeInt(i: i64): Node;
VAR result: Node;
BEGIN NEW(result);
  result.prev := 0;
  result.next := IntNode;
  result.v1   := i;
  result.v2   := 0;
RETURN result END MakeInt;

PROCEDURE MakeLink(l: Node): Node;
VAR result: Node;
BEGIN NEW(result);
  result.prev := 0;
  result.next := LinkNode;
  result.v1   := SYSTEM.VAL(i64, l);
  result.v2   := 0;
  l.prev := SYSTEM.VAL(i64, result) + 1;
RETURN result END MakeLink;

PROCEDURE MakeCopy(n: Node): Node;
VAR result: Node;
BEGIN NEW(result);
  result.prev := 0;
  result.next := TypeOf(n.next);
  result.v1   := n.v1;
  result.v2   := n.v2;
RETURN result END MakeCopy;

PROCEDURE Push(n: Node);
VAR copy: Node;
BEGIN
  copy := MakeCopy(n);
  IF Stack # NIL THEN Stack.prev := SYSTEM.VAL(i64, copy) END;
  copy.next  := SYSTEM.VAL(i64, Stack) + TypeOf(copy.next);
  Stack := copy;
END Push;

PROCEDURE Scrap(scrap: Node);
BEGIN
  scrap.prev := 0;
  scrap.next := SYSTEM.VAL(i64, Free);
  scrap.v1 := 0;
  scrap.v2 := 0;
  Free := scrap;
END Scrap;

PROCEDURE Drop;
VAR scrap: Node;
BEGIN
  scrap := Stack;
  Stack := NodeOf(Stack.next);
  Scrap(scrap)
END Drop;

PROCEDURE AddNode(list, newnode: Node);
VAR forward: i64;
BEGIN
  list.next := (list.next MOD 16) + (SYSTEM.VAL(i64, newnode));
  newnode.prev := SYSTEM.VAL(i64, list);
END AddNode;

PROCEDURE Constant(n: Node): Node;
VAR value, next: Node;
BEGIN
  value := NodeOf(n.next);
  next  := NodeOf(value.next);
  Push(value);
RETURN next END Constant;

PROCEDURE DumpList(n: Node);
VAR next: Node;
BEGIN
  WHILE n # NIL DO
    next := NodeOf(n.next); (* Default behavior *)
    CASE TypeOf(n.next) OF
    | IntNode:  wc('<'); wi(n.v1); wc('>')
    | LinkNode: wc('['); DumpList(NodeOf(n.next)); wc(']'); next := NodeOf(n.v1)
    | GenNode:  ws("[#GENERATOR#]")
    ELSE        ws("[#FAULTY#]");
    END;
    n := next;
  END;
END DumpList;

PROCEDURE Print;
BEGIN
  CASE TypeOf(Stack.next) OF
    | IntNode:  wi(Stack.v1)
    | LinkNode: wc('['); DumpList(NodeOf(Stack.v1)); wc(']')
    | GenNode:  ws("[#GENERATOR#]")
    ELSE        ws("[#FAULTY#]");
  END;
  Drop
END Print;

PROCEDURE Add;
VAR next: Node;
BEGIN
  next := NodeOf(Stack.next);
  IF (TypeOf(Stack.next) = IntNode) & (TypeOf(next.next) = IntNode) THEN
    next.v1 := Stack.v1 + next.v1;
    Drop
  ELSE
    Drop; Drop; Push(MakeInt(0))
  END
END Add;

PROCEDURE WIntrinsic(i: i64);
BEGIN
  CASE i OF
  | CoreFault:    ws("CoreFault");
  | CoreConstant: ws("CoreConstant");
  | CorePrint:    ws("CorePrint");
  | CoreAdd:      ws("CoreAdd");
  ELSE            ws("Unrecognised intrinsic");
  END
END WIntrinsic;

PROCEDURE Intrinsic(n: Node): Node;
VAR next: Node;
BEGIN
  next := NodeOf(n.next); (* Default behavior *)
  (* ws("Intrinsic "); WIntrinsic(n.v1); wsl("."); *)
  CASE n.v1 OF
  | CoreFault:    ws("Fault: intrinsic 0.")
  | CoreConstant: next := Constant(n)
  | CorePrint:    Print
  | CoreAdd:      Add
  ELSE Fail("Execute undefined intrinsic.")
  END;
RETURN next END Intrinsic;

PROCEDURE Execute(n: Node);
VAR next: Node;
BEGIN
  WHILE n # NIL DO
    (* ws("Execute "); DumpNode(n); *)
    next := NodeOf(n.next); (* Default behavior *)
    CASE TypeOf(n.next) OF
    | IntNode:  next := Intrinsic(n)
    | LinkNode: Push(n)
    | GenNode:  ws("[#GENERATOR#]")
    ELSE        Fail("Execute encountered faulty node.")
    END;
    n := next;
  END
END Execute;


PROCEDURE DumpListNodes(n: Node);
VAR next: Node;
BEGIN
  WHILE n # NIL DO
    next := NodeOf(n.next); (* Default behavior *)
    DumpNode(n);
    n := next;
  END;
END DumpListNodes;


PROCEDURE StringToList(s: ARRAY OF CHAR): Node;
VAR n1, n2, result: Node; i: i64;
BEGIN
  result := MakeInt(ORD(s[0]));
  n1 := result;
  FOR i := 1 TO LEN(s)-1 DO
    n2 := MakeInt(ORD(s[i]));
    AddNode(n1, n2);
    n1 := n2
  END;
RETURN result END StringToList;

PROCEDURE MatchInt(n1, n2: Node): Node;
(* Return node in store starting at n1 that matches n2 *)
VAR result: Node;
BEGIN
  result := NIL;
  wsl("MatchInt n1:"); DumpNode(n1);
  wsl("MatchInt n2:"); DumpNode(n2);
  IF TypeOf(n2.next) = IntNode THEN
    IF TypeOf(n1.next) = IntNode THEN
      IF n1.v1 = n2.v1 THEN result := n1 END
    ELSIF TypeOf(n1.next) = LinkNode THEN
      result := MatchInt(NodeOf(n1.next), n2);
      IF result = NIL THEN
        result := MatchInt(NodeOf(n1.v1), n2)
      END
    END
  END;
  ws("  result: "); wx(SYSTEM.VAL(i64, result), 16); wsl(".");
RETURN result END MatchInt;

PROCEDURE Save(n: Node);
VAR n1, n2: Node;
BEGIN
  IF Store = NIL THEN
    Store := n
  ELSE
    n1 := Store;
    n2 := MatchInt(n1, n);
    WHILE n2 # NIL DO
      n1 := NodeOf(n2.next);
      n  := NodeOf(n.next);
      n2 := MatchInt(n1, n)
    END;
    (* Add remainder of n as alternative to at n1 *)
    ws("Add remainder of n("); wx(SYSTEM.VAL(i64, n), 16);
    ws(") as alternative to n1("); wx(SYSTEM.VAL(i64, n1), 16);
    ws(") at n1.prev("); wx(SYSTEM.VAL(i64, n1.prev), 16);
    wsl(".");
    n2 := MakeLink(n1);
    AddNode(n2, n);
    AddNode(NodeOf(n1.prev), n2)
  END
END Save;


PROCEDURE TestAddNode;
VAR n1, n2, n3, n4: Node;
BEGIN
  wsl("Folio test.");
  ws("SIZE(i64) "); wi(SIZE(i64)); wsl(".");
  wsl("MakeInt n1.");  n1 := MakeInt(48+1);
  wsl("MakeInt n3.");  n3 := MakeInt(48+2);
  wsl("MakeInt n4.");  n4 := MakeInt(48+3);
  wsl("MakeLink n2."); n2 := MakeLink(n4);
  AddNode(n1, n2);
  AddNode(n2, n3);
  wsl("n1:"); DumpNode(n1);
  wsl("n2:"); DumpNode(n2);
  wsl("n3:"); DumpNode(n3);
  wsl("n4:"); DumpNode(n4);
  DumpList(n1); wl;

  Scrap(n1); Scrap(n2); Scrap(n3); Scrap(n4);
END TestAddNode;

PROCEDURE TestExecute;
VAR n1, n2, n3, n4, n5, n6: Node;
BEGIN
  n1 := MakeInt(CoreConstant);                  n2 := MakeInt(2); AddNode(n1, n2);
  n3 := MakeInt(CoreConstant); AddNode(n2, n3); n4 := MakeInt(3); AddNode(n3, n4);
  n5 := MakeInt(CoreAdd);      AddNode(n4, n5);
  n6 := MakeInt(CorePrint);    AddNode(n5, n6);
  (* DumpListNodes(n1); wl; *)
  Execute(n1); wl;
END TestExecute;

PROCEDURE TestStore;
BEGIN
  Save(StringToList("The cat")); (* sat on the mat.")); *)
  Save(StringToList("The cow")); (* jumped over the moon.")); *)
  DumpListNodes(Store);
END TestStore;

BEGIN Abort:=FALSE; Stack:=NIL; Free := NIL; Store := NIL;
  TestAddNode;
  TestExecute;
  TestStore;
END folio.
