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

IMPORT Strings, TextWriter, SYSTEM;


CONST
  (* Intrinsic instructions *)
  CoreFault    = 0;
  CoreConstant = 1;
  CorePrint    = 2;
  CoreAdd      = 3;


TYPE
  i64 = SYSTEM.INT64;

  Node = POINTER TO NodeDesc;
  NodeDesc = RECORD
    prev: Node;
    next: Node;
  END;

  IntegerNode = POINTER TO IntegerNodeDesc;
  IntegerNodeDesc = RECORD (NodeDesc) i: i64  END;

  LinkNode = POINTER TO LinkNodeDesc;
  LinkNodeDesc = RECORD (NodeDesc) l: Node END;

  GeneratorNodeDesc = RECORD (NodeDesc) (* todo *) END;


VAR
   Abort: BOOLEAN;
   Stack: Node;
   Store: LinkNode;


(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)              END ws;
PROCEDURE wc(c: CHAR);           BEGIN TextWriter.Char(c)                END wc;
PROCEDURE wl;                    BEGIN TextWriter.NewLine                END wl;
PROCEDURE wi(i: LONGINT);        BEGIN TextWriter.Integer(i)             END wi;
PROCEDURE wx(i,n: LONGINT);      BEGIN TextWriter.Hex(i,n)               END wx;
PROCEDURE wnb;                   BEGIN TextWriter.NoBreak                END wnb;
PROCEDURE wlc;                   BEGIN TextWriter.StartLine              END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl                         END wsl;
PROCEDURE space(i: LONGINT);     BEGIN WHILE i>0 DO ws("  "); DEC(i) END END space;


(* ----------------- Error handling convenience functions ------------------- *)

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN
  IF Strings.Length(msg) > 0 THEN wlc; ws("Internal error:"); wsl(msg)END;
  wlc;
  HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* ------------------------------- Dump nodes ------------------------------- *)

PROCEDURE DumpInt(i: i64);
BEGIN
  wi(i);
  IF (i >= 32) & (i < 127) THEN
    ws(" '"); wc(CHR(i)); wc("'")
  END
END DumpInt;

PROCEDURE DumpNode(n: Node);
BEGIN
  ws("Node at "); wx(SYSTEM.VAL(i64, n),      16);
  ws(", prev: "); wx(SYSTEM.VAL(i64, n.prev), 16);
  ws(", next: "); wx(SYSTEM.VAL(i64, n.next), 16);
  ws(", is ");
  WITH
    n: IntegerNode DO ws("integer, i: "); DumpInt(n.i)
  | n: LinkNode    DO ws("link, l: "); wx(SYSTEM.VAL(i64, n.l), 16)
  ELSE                ws("unknown")
  END;
  wsl(".")
END DumpNode;

PROCEDURE DumpListNodes(n: Node; depth: i64);
BEGIN
  WHILE n # NIL DO
    space(depth); DumpNode(n);
    IF n IS LinkNode THEN
      space(depth); wsl("[");
      DumpListNodes(n(LinkNode).l, depth+1);
      space(depth); wsl("]")
    END;
    n := n.next
  END;
END DumpListNodes;

PROCEDURE DumpList(n: Node);
BEGIN
  WHILE n # NIL DO
    IF n IS IntegerNode THEN
      wc('<'); DumpInt(n(IntegerNode).i); wc('>'); n := n.next
    ELSIF n IS LinkNode THEN
      wc('['); DumpList(n(LinkNode).next); wc(']'); n := n(LinkNode).l
    ELSE
      ws("[#FAULTY#]"); n := n.next
    END
  END;
END DumpList;


(* --------------------------- Node construction ---------------------------- *)

PROCEDURE MakeCopy(n: Node): Node;
VAR i: IntegerNode; l: LinkNode;
BEGIN
  WITH
    n: IntegerNode DO NEW(i); i.i := n.i; RETURN i
  | n: LinkNode DO    NEW(l); l.l := n.l; RETURN l
  ELSE                Fail("MakeCopy passed neither integer nor link node.")
  END
END MakeCopy;


(* ------------------------------ Node stacking ----------------------------- *)

PROCEDURE BreakBefore(n: Node);
BEGIN IF (n # NIL) & (n.prev # NIL) THEN n.prev.next := NIL; n.prev := NIL END
END BreakBefore;

PROCEDURE Join(n1, n2: Node);
(* Link n1 to n2 via n1.next and n2.prev.
   If n1.next is already not nil, add a link node between n1 and n2
   whose link references the old n1.next. *)
VAR link: LinkNode;
BEGIN
  IF n2 # NIL THEN
    IF n1.next # NIL THEN
      NEW(link);
      link.l  := n1.next;  n1.next.prev := link;
      n1.next := link;     link.prev    := n1;
      n1 := link;
    END;
    n1.next := n2; n2.prev := n1
  END
END Join;

PROCEDURE Push(n: Node);
VAR copy: Node;
BEGIN copy := MakeCopy(n); Join(copy, Stack); Stack := copy;
END Push;

PROCEDURE Drop;
BEGIN Stack := Stack.next; BreakBefore(Stack)
END Drop;

PROCEDURE Swap;
VAR n1, n2, n3: Node;
BEGIN
  n2 := Stack;  n1 := n2.next;  n3 := n1.next;
  (* Relink in the order n1 n2 n3 *)
  n1.prev := NIL;  n1.next := n2;
  n2.prev := n1;   n2.next := n3;
  IF n3 # NIL THEN n3.prev := n2 END;
  Stack := n1;
END Swap;


(* ------------------------------- Intrinsics ------------------------------- *)

PROCEDURE Constant(n: Node): Node;
BEGIN n := n.next; Push(n);
RETURN n.next END Constant;

PROCEDURE Print;
BEGIN
  IF Stack IS IntegerNode THEN wi(Stack(IntegerNode).i)
  ELSIF Stack IS LinkNode THEN wc('['); DumpList(Stack(LinkNode).l); wc(']')
  ELSE ws("[#FAULTY#]")
  END;
  Drop;
END Print;

PROCEDURE AddIntToList(i: i64; n: Node);
BEGIN
  WHILE n # NIL DO
    WITH n: IntegerNode DO INC(n.i, i)
    ELSE AddIntToList(i, n(LinkNode).l)
    END;
    n := n.next
  END
END AddIntToList;

PROCEDURE AddListToList(n1, n2: Node);
BEGIN
  WHILE (n1 # NIL) & (n2 # NIL) DO
    IF n1 IS IntegerNode THEN
      IF n2 IS IntegerNode THEN
        INC(n2(IntegerNode).i, n1(IntegerNode).i)
      ELSE (* n2 is link node *)
        AddIntToList(n1(IntegerNode).i, n2(LinkNode).l)
      END
    ELSE (* n1 is link node *)
      IF n2 IS IntegerNode THEN
        AddIntToList(n2(IntegerNode).i, n1(LinkNode).l)
      ELSE (* n2 is link node *)
        AddListToList(n1(LinkNode).l, n2(LinkNode).l)
      END
    END;
    n1 := n1.next;
    n2 := n2.next
  END
END AddListToList;

PROCEDURE Add;
BEGIN
  IF (Stack IS IntegerNode) = (Stack.next IS IntegerNode) THEN
    IF Stack IS IntegerNode THEN
      INC(Stack.next(IntegerNode).i, Stack(IntegerNode).i)
    ELSE
      AddListToList(Stack(LinkNode).l, Stack.next(LinkNode).l)
    END
  ELSE (* One is int, one is list *)
    IF Stack.next IS IntegerNode THEN Swap END;
    AddIntToList(Stack(IntegerNode).i, Stack.next(LinkNode).l)
  END;
  Drop
END Add;


PROCEDURE Intrinsic(n: IntegerNode): Node;
VAR next: Node;
BEGIN
  next := n.next; (* Default behavior *)
  (* ws("Intrinsic: "); wi(n.i); wsl('.'); *)
  CASE n.i OF
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
    next := n.next; (* Default behavior *)
    WITH
      n: IntegerNode DO next := Intrinsic(n)
    | n: LinkNode    DO Push(n)
    ELSE                Fail("Execute encountered faulty node.")
    END;
    n := next;
  END
END Execute;


(* --------------------------------- Store ---------------------------------- *)

PROCEDURE MatchInt(n: Node; i: i64): Node;
(* Returns the IntegerNode with value i that matches starting
  at n, or NIL if there is no match.
  If n is an IntegerNode it's a simple value test.
  If n is a LinkNode it's a recursive search for a match through
  both the .l and .next links. *)
VAR result: Node;
BEGIN result := NIL;
  IF n # NIL THEN
    IF (n IS IntegerNode) & (n(IntegerNode).i = i) THEN
      result := n
    ELSIF n IS LinkNode THEN
      result := MatchInt(n(LinkNode).l, i);
      IF result = NIL THEN result := MatchInt(n.next, i) END
    END
  END;
RETURN result END MatchInt;

PROCEDURE MatchNode(store, list: Node): Node;
BEGIN
  IF (list = NIL) OR ~(list IS IntegerNode) THEN RETURN NIL END;
  RETURN MatchInt(store, list(IntegerNode).i)
END MatchNode;

PROCEDURE MatchStore(VAR store, list: Node);
(* Advances store and list forward while store.next matches list *)
(* Entry: store.next is where to start searching the store *)
(* Exit:  store is the node to which the remainder of list should be joined *)
VAR match: Node;
BEGIN
  match := MatchNode(store.next, list);
  WHILE match # NIL DO
    store := match;
    list  := list.next;
    match := MatchNode(store.next, list)
  END
END MatchStore;

PROCEDURE Save(n: Node);
VAR s: Node;
BEGIN
  s := Store;
  MatchStore(s, n);
  Join(s, n)
END Save;


(* --------------------------------- Tests ---------------------------------- *)

PROCEDURE MakeInt(i: i64): IntegerNode;
VAR result: IntegerNode;
BEGIN NEW(result); result.i := i; RETURN result END MakeInt;

PROCEDURE MakeLink(l: Node): LinkNode;
VAR result: LinkNode;
BEGIN NEW(result); result.l := l; RETURN result END MakeLink;

PROCEDURE StringToList(s: ARRAY OF CHAR): Node;
VAR n1, n2, result: Node; i, l: i64;
BEGIN
  result := MakeInt(ORD(s[0]));
  n1 := result;
  l := Strings.Length(s);
  FOR i := 1 TO l-1 DO
    n2 := MakeInt(ORD(s[i]));
    Join(n1, n2);
    n1 := n2
  END;
RETURN result END StringToList;

PROCEDURE TestAddNode;
VAR n1, n2, n3, n4: Node;
BEGIN
  wsl("MakeInt n1.");  n1 := MakeInt(48+1);
  wsl("MakeInt n3.");  n3 := MakeInt(48+2);
  wsl("MakeInt n4.");  n4 := MakeInt(48+3);
  wsl("MakeLink n2."); n2 := MakeLink(n4);
  Join(n1, n2);
  Join(n2, n3);
  ws("n1:"); DumpNode(n1);
  ws("n2:"); DumpNode(n2);
  ws("n3:"); DumpNode(n3);
  ws("n4:"); DumpNode(n4);
  DumpList(n1); wl;
END TestAddNode;

PROCEDURE VerifyLinks(first: Node);
VAR n: Node;
BEGIN n := first;
  WHILE n # NIL DO
    Assert((n.next = NIL) OR (n.next.prev = n), "n.next.prev = n");
    WITH n: LinkNode DO
      Assert((n.l = NIL) OR (n.l.prev = n), "n.l.prev = n");
      VerifyLinks(n.l)
    ELSE END;
    n := n.next;
  END
END VerifyLinks;

PROCEDURE TestExecute;
VAR n1, n2, n3, n4, n5, n6: Node;
BEGIN
  n1 := MakeInt(CoreConstant);
  n2 := MakeInt(2);            Join(n1, n2);
  n3 := MakeInt(CoreConstant); Join(n2, n3);
  n4 := MakeInt(3);            Join(n3, n4);
  n5 := MakeInt(CoreAdd);      Join(n4, n5);
  n6 := MakeInt(CorePrint);    Join(n5, n6);
  DumpListNodes(n1,0); wl;
  VerifyLinks(Stack);
  Execute(n1); wl;
  VerifyLinks(Stack);
END TestExecute;


PROCEDURE PrintStore(n: Node; column: i64);
TYPE
  pending = POINTER TO pendingDesc;
  pendingDesc = RECORD
    next: pending;
    node: Node;
    column: i64;
  END;
VAR
  stack, p: pending;
  i:        i64;
BEGIN
  stack := NIL;
  FOR i := 1 TO column DO wc(".") END;
  WHILE n # NIL DO
    WITH
      n: IntegerNode DO
        IF (n.i > 31) & (n.i < 127) THEN wc(CHR(n.i)) ELSE wc("?") END;
        INC(column);
    | n: LinkNode DO
        NEW(p); p.node := n.l; p.column := column; p.next := stack; stack := p;
    END;
    n := n.next
  END;
  wl;
  WHILE stack # NIL DO
    PrintStore(stack.node, stack.column);
    stack := stack.next;
  END
END PrintStore;

PROCEDURE TestLookup(s: ARRAY OF CHAR);
VAR store, key: Node;
BEGIN
  ws("TestLookup('"); ws(s);
  key := StringToList(s);
  store := Store;
  MatchStore(store, key);
  IF key # NIL THEN
    wsl("') not found.");
  ELSE
    wsl("') found:");
    PrintStore(store.next,2)
  END
END TestLookup;

PROCEDURE TestStore;
VAR s,n: Node;
BEGIN
  Save(StringToList("The cat sat on the mat."));
  Save(StringToList("The cow jumped over the moon."));
  Save(StringToList("Another line altogether."));
  Save(StringToList("The quick brown fox jumps over the lazy dog."));
  Save(StringToList("The little dog laughed to see such fun."));
  Save(StringToList("The dish ran away with the spoon."));
  (* DumpListNodes(Store, 0); *)
  VerifyLinks(Store);
  PrintStore(Store, 0);
  TestLookup("splurd");
  TestLookup("The cat");
  TestLookup("The");
  TestLookup("An");
END TestStore;

PROCEDURE TestSwap;
BEGIN
  Push(MakeInt(1));
  Push(MakeInt(2));
  wsl("Before swap:"); DumpListNodes(Stack,2); VerifyLinks(Stack);
  Swap;
  wsl("After swap:");  DumpListNodes(Stack,2); VerifyLinks(Stack);
END TestSwap;

BEGIN Abort:=FALSE; Stack:=NIL; NEW(Store);
  wsl("Folio test.");
  IF SIZE(i64) # 8 THEN
    ws("SIZE(i64) = "); wi(SIZE(i64)); ws(", must be 8."); Fail("")
  END;
  TestAddNode;
  TestExecute;
  TestStore;
  TestSwap;
END folio.
