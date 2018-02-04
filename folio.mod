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
   Store: Node;


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
BEGIN wlc; ws("Internal error:"); wsl(msg); HALT(99)
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

PROCEDURE DumpListNodes(first: Node; depth: i64);
VAR n: Node;
BEGIN
  n := first;
  WHILE n # NIL DO
    space(depth); DumpNode(n);
    WITH n: LinkNode DO
      space(depth); wsl("[");
      DumpListNodes(n.l, depth+1);
      space(depth); wsl("]");
    ELSE
    END;
    n := n.next
  END;
END DumpListNodes;

PROCEDURE DumpList(n: Node);
VAR this, next: Node;
BEGIN
  this := n;
  WHILE this # NIL DO
    next := this.next; (* Default behavior *)
    WITH
      this: IntegerNode DO wc('<'); wi(this.i); wc('>')
    | this: LinkNode    DO wc('['); DumpList(this.next); wc(']');
                           next := this.l
    ELSE ws("[#FAULTY#]");
    END;
    this := next;
  END;
END DumpList;


(* --------------------------- Node construction ---------------------------- *)

PROCEDURE MakeInt(i: i64): IntegerNode;
VAR result: IntegerNode;
BEGIN NEW(result); result.i := i; RETURN result END MakeInt;

PROCEDURE MakeLink(l: Node): LinkNode;
VAR result: LinkNode;
BEGIN NEW(result); result.l := l; RETURN result END MakeLink;

PROCEDURE MakeCopy(n: Node): Node;
VAR result: Node;
BEGIN
  WITH
    n: IntegerNode DO result := MakeInt(n.i)
  | n: LinkNode DO    result := MakeLink(n.l)
  ELSE                Fail("MakeCopy passed neither integer nor link node.")
  END;
RETURN result END MakeCopy;


(* ------------------------------ Node stacking ----------------------------- *)

PROCEDURE Push(n: Node);
VAR copy: Node;
BEGIN
  copy := MakeCopy(n);
  IF Stack # NIL THEN Stack.prev := copy END;
  copy.next := Stack;
  Stack := copy;
END Push;

PROCEDURE Drop;
BEGIN
  Stack := Stack.next;
  IF Stack # NIL THEN Stack.prev := NIL END
END Drop;

PROCEDURE Connect(list, newnode: Node);
BEGIN
  list.next := newnode;
  newnode.prev := list
END Connect;


(* ------------------------------- Intrinsics ------------------------------- *)

PROCEDURE Constant(n: Node): Node;
BEGIN n := n.next; Push(n);
RETURN n.next END Constant;

PROCEDURE Print;
VAR top: Node;
BEGIN
  top := Stack;
  WITH
    top: IntegerNode DO wi(top.i)
  | top: LinkNode    DO wc('['); DumpList(top.l); wc(']')
  ELSE                    ws("[#FAULTY#]");
  END;
  Drop;
END Print;

PROCEDURE Add;
VAR top, next: Node; sum: i64;
BEGIN
  top  := Stack;
  next := Stack.next;
  sum  := 0;
  WITH top: IntegerNode DO
    WITH next: IntegerNode DO
      next.i := top.i + next.i; Drop; RETURN
    ELSE
    END
  ELSE
  END;
  Drop; Drop; Push(MakeInt(0))
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
    next :=n.next; (* Default behavior *)
    WITH
      n: IntegerNode DO next := Intrinsic(n)
    | n: LinkNode    DO Push(n)
    ELSE                Fail("Execute encountered faulty node.")
    END;
    n := next;
  END
END Execute;


(* --------------------------------- Store ---------------------------------- *)

PROCEDURE MatchInt(store: Node; i: i64): Node;
(* Returns the IntegerNode with value i that matches starting
  at n, or NIL if there is no match.
  If n is an IntegerNode it's a simple value test.
  If n is a LinkNode it's a recursive search for a match through
  both the .l and .next links. *)
VAR n, result: Node;
BEGIN n := store; result := NIL;
  IF n # NIL THEN
    WITH
      n: IntegerNode DO
        IF n.i = i THEN result := n END
    | n: LinkNode DO
        result := MatchInt(n.l, i);
        IF result = NIL THEN result := MatchInt(n.next, i) END
    END
  END;
RETURN result END MatchInt;

PROCEDURE MatchNode(store, list: Node): Node;
BEGIN
  IF (list = NIL) OR ~(list IS IntegerNode) THEN RETURN NIL END;
  WITH list: IntegerNode DO RETURN MatchInt(store, list.i) END
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

PROCEDURE Save(n: Node);
VAR s: Node;
BEGIN
  s := Store;
  MatchStore(s, n);
  Join(s, n)
END Save;


(* --------------------------------- Tests ---------------------------------- *)

PROCEDURE StringToList(s: ARRAY OF CHAR): Node;
VAR n1, n2, result: Node; i, l: i64;
BEGIN
  result := MakeInt(ORD(s[0]));
  n1 := result;
  l := Strings.Length(s);
  FOR i := 1 TO l-1 DO
    n2 := MakeInt(ORD(s[i]));
    Connect(n1, n2);
    n1 := n2
  END;
RETURN result END StringToList;

PROCEDURE TestAddNode;
VAR n1, n2, n3, n4: Node;
BEGIN
  wsl("Folio test.");
  ws("SIZE(i64) "); wi(SIZE(i64)); wsl(".");
  wsl("MakeInt n1.");  n1 := MakeInt(48+1);
  wsl("MakeInt n3.");  n3 := MakeInt(48+2);
  wsl("MakeInt n4.");  n4 := MakeInt(48+3);
  wsl("MakeLink n2."); n2 := MakeLink(n4);
  Connect(n1, n2);
  Connect(n2, n3);
  wsl("n1:"); DumpNode(n1);
  wsl("n2:"); DumpNode(n2);
  wsl("n3:"); DumpNode(n3);
  wsl("n4:"); DumpNode(n4);
  DumpList(n1); wl;
END TestAddNode;

PROCEDURE TestExecute;
VAR n1, n2, n3, n4, n5, n6: Node;
BEGIN
  n1 := MakeInt(CoreConstant);                     n2 := MakeInt(2); Connect(n1, n2);
  n3 := MakeInt(CoreConstant); Connect(n2, n3); n4 := MakeInt(3); Connect(n3, n4);
  n5 := MakeInt(CoreAdd);      Connect(n4, n5);
  n6 := MakeInt(CorePrint);    Connect(n5, n6);
  DumpListNodes(n1,0); wl;
  Execute(n1); wl;
END TestExecute;


PROCEDURE PrintStore(first: Node; column: i64);
TYPE
  pending = POINTER TO pendingDesc;
  pendingDesc = RECORD
    next: pending;
    node: Node;
    column: i64;
  END;
VAR
  n:        Node;
  stack, p: pending;
  i:        i64;
BEGIN
  n := first;
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

BEGIN Abort:=FALSE; Stack:=NIL; Store := MakeLink(NIL);
  TestAddNode;
  TestExecute;
  TestStore;
END folio.
