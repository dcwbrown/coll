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
  DoFault     = 0;
  DoNoOp      = 1;
  DoHere      = 2;
  DoPrint     = 3;
  DoAdd       = 4;
  DoSymbol    = 5;
  DoDup       = 6;
  DoParseNest = 7;


TYPE
  i64 = SYSTEM.INT64;

  Node = POINTER TO NodeDesc;
  NodeDesc = RECORD
    prev: Node;
    next: Node;
  END;

  IntegerNode = POINTER TO IntegerNodeDesc;
  IntegerNodeDesc = RECORD (NodeDesc) i: i64  END;

  InstructionNode = POINTER TO InstructionNodeDesc;
  InstructionNodeDesc = RECORD (NodeDesc) i: i64  END;

  LinkNode = POINTER TO LinkNodeDesc;
  LinkNodeDesc = RECORD (NodeDesc) l: Node END;



VAR
   Abort:  BOOLEAN;
   Stack:  Node;
   Store:  LinkNode;
   Input:  LinkNode;
   Output: LinkNode;


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

PROCEDURE PrintInstruction(i: i64);
BEGIN
  CASE i OF
  | DoFault:     ws("<Fault: intrinsic 0>")
  | DoNoOp:      ws("<NoOp>")
  | DoHere:      ws("<Here>")
  | DoPrint:     ws("<Print>")
  | DoAdd:       ws("<Add>")
  | DoDup:       ws("<Dup>")
  | DoParseNest: ws("<ParseNest>")
  | DoSymbol:    ws("<Symbol>")
  ELSE           ws("<undefined intrinsic>")
  END;
END PrintInstruction;


(* Print list with integers used as chars where possible *)

PROCEDURE PrintInt(i: i64);
BEGIN
  IF (i>=32) & (i<=126) THEN wc(CHR(i)) ELSE wc("<"); wi(i); wc(">") END
END PrintInt;

PROCEDURE PrintSymbol(n: Node);
BEGIN
  WHILE (n # NIL) & (n IS LinkNode) DO n := n.prev END;
  IF n = NIL THEN RETURN END;
  IF n.prev # NIL THEN PrintSymbol(n.prev) END;
  WITH
    n: IntegerNode     DO PrintInt(n.i)
  | n: InstructionNode DO PrintInstruction(n.i)
  ELSE ws("[#FAULTY#]")
  END
END PrintSymbol;

PROCEDURE ^PrintList(n: Node);

PROCEDURE PrintLink(l: Node);
BEGIN wc('['); PrintList(l); wc(']')
END PrintLink;

PROCEDURE PrintList(n: Node);
VAR i: i64;
BEGIN
  WHILE n # NIL DO
    WITH
      n: LinkNode        DO PrintLink(n.l)
    | n: IntegerNode     DO PrintInt(n.i)
    | n: InstructionNode DO
      IF n.i = DoSymbol THEN
        ws("<Symbol: "); PrintSymbol(n.prev); wc('>')
      ELSE
        PrintInstruction(n.i)
      END
    ELSE ws("[#FAULTY#]")
    END;
    n := n.next
  END;
END PrintList;

(* Dump simple format multiple nodes per line *)

PROCEDURE DumpList(n: Node);
BEGIN
  WHILE n # NIL DO
    IF n IS LinkNode           THEN wc('['); DumpList(n(LinkNode).l); wc(']')
    ELSIF n IS IntegerNode     THEN wc('<'); DumpInt(n(IntegerNode).i); wc('>')
    ELSIF n IS InstructionNode THEN PrintInstruction(n(InstructionNode).i)
    ELSE ws("[#FAULTY#]")
    END;
    n := n.next
  END;
END DumpList;

(* Dump node details on a whole line. *)

PROCEDURE DumpNode(n: Node);
BEGIN
  IF n = NIL THEN wsl("NIL."); RETURN END;
  ws("Node at "); wx(SYSTEM.VAL(i64, n),      16);
  ws(", prev: "); wx(SYSTEM.VAL(i64, n.prev), 16);
  ws(", next: "); wx(SYSTEM.VAL(i64, n.next), 16);
  ws(", is ");
  WITH
    n: IntegerNode     DO ws("integer, i: "); DumpInt(n.i)
  | n: InstructionNode DO ws("instruction, i: "); wi(n.i); ws(" - "); PrintInstruction(n.i)
  | n: LinkNode        DO ws("link, l: "); wx(SYSTEM.VAL(i64, n.l), 16)
  ELSE                    ws("unknown")
  END;
  wsl(".")
END DumpNode;

PROCEDURE DumpNodeList(n: Node; depth: i64);
BEGIN
  WHILE n # NIL DO
    space(depth); DumpNode(n);
    IF n IS LinkNode THEN
      space(depth); wsl("[");
      DumpNodeList(n(LinkNode).l, depth+1);
      space(depth); wsl("]")
    END;
    n := n.next
  END;
END DumpNodeList;



(* --------------------------- Node construction ---------------------------- *)

PROCEDURE MakeCopy(n: Node): Node;
VAR i: IntegerNode; l: LinkNode; o: InstructionNode;
BEGIN
  WITH
    n: IntegerNode     DO NEW(i); i.i := n.i; RETURN i
  | n: InstructionNode DO NEW(o); o.i := n.i; RETURN o
  | n: LinkNode        DO NEW(l); l.l := n.l; RETURN l
  ELSE                    Fail("MakeCopy passed neither integer, instruction nor link node.")
  END
END MakeCopy;


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

(* ------------------------------ Node stacking ----------------------------- *)

PROCEDURE Push(n: Node);
VAR copy: Node;
BEGIN copy := MakeCopy(n); Join(copy, Stack); Stack := copy;
END Push;

PROCEDURE Dup;   BEGIN Push(Stack) END Dup;
PROCEDURE Drop;  BEGIN Stack := Stack.next; BreakBefore(Stack) END Drop;

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

(*
PROCEDURE Constant(n: Node): Node;
BEGIN n := n.next; Push(n);
RETURN n.next END Constant;
*)

PROCEDURE Print;
BEGIN
  IF    Stack IS IntegerNode     THEN wi(Stack(IntegerNode).i)
  ELSIF Stack IS InstructionNode THEN PrintInstruction(Stack(InstructionNode).i)
  ELSIF Stack IS LinkNode        THEN wc('['); DumpList(Stack(LinkNode).l); wc(']')
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


PROCEDURE MakeInstruction(i: i64): InstructionNode;
VAR result: InstructionNode;
BEGIN NEW(result); result.i := i; RETURN result END MakeInstruction;

PROCEDURE MakeLink(l: Node): LinkNode;
VAR result: LinkNode;
BEGIN NEW(result); result.l := l; RETURN result END MakeLink;

PROCEDURE ^ParseNest;

PROCEDURE Intrinsic(n: InstructionNode): Node;
VAR next: Node;
BEGIN
  next := n.next; (* Default behavior *)
  (* ws("Intrinsic: "); wi(n.i); wsl('.'); *)
  CASE n.i OF
  | DoFault:     ws("Fault: intrinsic 0.")
  | DoNoOp:
  | DoHere:      wlc; wsl("Here!")
  | DoPrint:     Print
  | DoAdd:       Add
  | DoDup:       Dup
  | DoParseNest: ParseNest
  | DoSymbol:    Push(MakeLink(n))
  ELSE Fail("Execute undefined intrinsic.")
  END;
RETURN next END Intrinsic;

PROCEDURE Execute(n: Node);
BEGIN
  WHILE n # NIL DO
    IF n IS InstructionNode THEN
      n := Intrinsic(n(InstructionNode))
    ELSE
      Push(n); n := n.next
    END
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


(* -------------------------------- Parsing --------------------------------- *)

PROCEDURE IsWhiteSpace(n: Node): BOOLEAN;
BEGIN RETURN (n IS IntegerNode) & (n(IntegerNode).i <= 32) END IsWhiteSpace;

PROCEDURE IsAlphanumeric(n: Node): BOOLEAN;
BEGIN
  (* wsl("IsAlphanumericNode."); *)
  WITH n: IntegerNode DO RETURN
       (n.i >= ORD('0'))
    & ((n.i <= ORD('9')) OR (n.i >= ORD('A')))
    & ((n.i <= ORD('Z')) OR (n.i >= ORD('a')))
    &  (n.i <= ORD('z'));
  ELSE RETURN FALSE
  END
END IsAlphanumeric;

PROCEDURE IsCharacter(n: Node; c: CHAR): BOOLEAN;
BEGIN WITH n: IntegerNode DO RETURN n.i = ORD(c) ELSE RETURN FALSE END
END IsCharacter;

PROCEDURE MatchAnyInstruction(n: Node): Node;
(* Returns an InstructionNode or NIL.
  If n is an InstructioNode, returns that.
  If n is an IntegerNode, returns NIL.
  If n is a LinkNode it's a recursive search for an instruction node through
  both the .l and .next links. *)
VAR result: Node;
BEGIN result := NIL;
  (* wsl("Begin MatchAnyInstruction."); *)
  IF n # NIL THEN
    IF n IS InstructionNode THEN
      result := n
    ELSIF n IS LinkNode THEN
      result := MatchAnyInstruction(n(LinkNode).l);
      IF result = NIL THEN result := MatchAnyInstruction(n.next) END
    END
  END;
RETURN result END MatchAnyInstruction;

PROCEDURE ParseNest;
VAR root: Node; depth: INTEGER;
BEGIN
  root := MakeLink(Input.l);
  depth := 1;
  WHILE (depth > 0) & (Input.l # NIL) DO
    IF    IsCharacter(Input.l, '[') THEN INC(depth)
    ELSIF IsCharacter(Input.l, ']') THEN DEC(depth);
      IF depth <= 0 THEN BreakBefore(Input.l) END (* Disconnect ']' *)
    END;
    Input.l := Input.l.next
  END;
  IF Input.l # NIL THEN Join(root, Input.l) END;
  Input.l := root;
END ParseNest;

PROCEDURE Parse;
(* Lookup each integer in the list starting at Input.l
   At end of each match check that the dictionary contains an
     instruction and execute it.
   Eat any white space.
   Repeat.
*)
VAR s, end: Node;
BEGIN
  WHILE Input.l # NIL DO
    IF Input.l IS LinkNode THEN
      Push(Input.l); Input.l := Input.l.next
    ELSIF Input.l IS InstructionNode THEN
      Input.l := Intrinsic(Input.l(InstructionNode))
    ELSIF Input.l IS IntegerNode THEN
      IF Input.l(IntegerNode).i <= 32 THEN
        Input.l := Input.l.next  (* Skip white space *)
      ELSE
        ws("Parsing: "); PrintList(Input.l); wl;
        IF Input.l # NIL THEN
          s := Store;
          end := Input.l;
          MatchStore(s, end);
          (*
          ws("MatchStore complete. s is "); DumpNode(s);
          ws(" ... end is "); DumpNode(end);
          *)

          IF end = Input.l THEN  (* Didn't match anything at all. *)
            wsl("Empty match.");
            s := NIL;
            IF ~IsAlphanumeric(end) THEN end := end.next
            ELSE WHILE (end # NIL) & IsAlphanumeric(end) DO end := end.next END
            END
          END;

          IF (end # NIL)       &  IsAlphanumeric(end)
          &  (end.prev # NIL)  &  IsAlphanumeric(end.prev) THEN
            (* If match stops between alphanumerics then it is not a proper match. *)
            s := NIL;
            (* Advance end to proper end of sequence of alphanumerics. *)
            WHILE (end # NIL) & IsAlphanumeric(end) DO end := end.next END
          END;

          (* Is match position a valid end of match? *)
          IF s # NIL THEN s := MatchAnyInstruction(s.next) END;

          (* If no match then we'll be adding the new word to the store as a
             symbol *)
          IF s = NIL THEN
            (* Temporarily use s to point to last character of new word, and
               break input at end of new word. *)
            IF end = NIL THEN
              (* Need to scan through input to find the last character. *)
              s := Input.l; WHILE s.next # NIL DO s := s.next END
            ELSE
              s := end.prev; s.next := NIL; end.prev := NIL
            END;
            (* ws("Add new symbol to store: "); PrintList(Input.l); wl; *)
            (* Append a DoSymbol instruction to make this a symbol, then
               add it to the store. *)
            ws("No match, adding: '"); PrintList(Input.l); wsl("'.");
            Join(s, MakeInstruction(DoSymbol));
            Save(Input.l);
            (* Exit with s addressing the DoSymbol instruction. *)
            s := s.next;
          END;
          (* ws("Execute: "); DumpList(s); wl; *)
          Input.l := end;  (* Advance over matched input *)
          Execute(s);      (* s is allowed to advance input.l if it so chooses. *)
        END
      END
    ELSE
      wlc; wsl("Unexpected node type in Parse source.");
      Input.l := Input.l.next;
    END
  END
END Parse;



(* --------------------------------- Tests ---------------------------------- *)

PROCEDURE MakeInteger(i: i64): IntegerNode;
VAR result: IntegerNode;
BEGIN NEW(result); result.i := i; RETURN result END MakeInteger;

(*
PROCEDURE SubstringToList(s: ARRAY OF CHAR; VAR i: i64; l: i64): Node;
VAR root, last, addition: Node;
BEGIN
  NEW(root); last := root;
  WHILE (i<l) & (s[i] # ']') DO
    IF s[i] = '[' THEN
      INC(i);
      addition := MakeLink(SubstringToList(s, i, l));
      addition(LinkNode).l.prev := addition
    ELSE
      addition := MakeInteger(ORD(s[i]));
      INC(i)
    END;
    Join(last, addition);
    last := last.next
  END;
  IF i<l THEN INC(i) END; ( * Step over ']' * )
RETURN root.next END SubstringToList;

PROCEDURE StringToList(s: ARRAY OF CHAR): Node;
VAR i, l: i64;
BEGIN i := 0; l := Strings.Length(s);
RETURN SubstringToList(s, i, l) END StringToList;
*)

PROCEDURE StringToList(s: ARRAY OF CHAR): Node;
VAR root, last: Node; i: i64;
BEGIN
  NEW(root);  last := root;  i := 0;
  WHILE (i<LEN(s)) & (s[i] # 0X) DO
    Join(last, MakeInteger(ORD(s[i])));
    last := last.next;
    INC(i)
  END;
RETURN root.next END StringToList;

PROCEDURE TestAddNode;
VAR n1, n2, n3, n4: Node;
BEGIN
  wsl("MakeInteger n1.");  n1 := MakeInteger(48+1);
  wsl("MakeInteger n3.");  n3 := MakeInteger(48+2);
  wsl("MakeInteger n4.");  n4 := MakeInteger(48+3);
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
VAR n1, n2, n3, n4: Node;
BEGIN
  n1 := MakeInteger(2);
  n2 := MakeInteger(3);            Join(n1, n2);
  n3 := MakeInstruction(DoAdd);    Join(n2, n3);
  n4 := MakeInstruction(DoPrint);  Join(n3, n4);
  DumpNodeList(n1,0); wl;
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
    | n: InstructionNode DO PrintInstruction(n.i)
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
  Save(StringToList("A list with a [nested] part."));

  (* DumpNodeList(Store, 0); *)
  VerifyLinks(Store);
  PrintStore(Store, 0);
  TestLookup("splurd");
  TestLookup("The cat");
  TestLookup("The");
  TestLookup("An");
END TestStore;

PROCEDURE TestSwap;
BEGIN
  Push(MakeInteger(1));
  Push(MakeInteger(2));
  wsl("Before swap:"); DumpNodeList(Stack,2); VerifyLinks(Stack);
  Swap;
  wsl("After swap:");  DumpNodeList(Stack,2); VerifyLinks(Stack);
END TestSwap;

PROCEDURE TestParse;
VAR n1, n2, n3, n4, n5: Node;
BEGIN
  Store := NIL;
  NEW(Store);
  n1 := MakeInteger(ORD('h'));
  n2 := MakeInteger(ORD('i'));   Join(n1,n2);
  n3 := MakeInstruction(DoHere); Join(n2,n3);
  Save(n1);
  PrintStore(Store,0);

  wsl("Test parse 'hi hi'");
  Input.l := StringToList("hi hi"); Parse;
  PrintStore(Store,0);

  wsl("Test parse 'the cat sat hi on the cat [nested part] the cat'");
  Stack := NIL;
  wsl("Store before parse:"); PrintStore(Store,0);
  Input.l := StringToList("the cat sat hi on the cat [nested part] the cat");
  Parse;
  ws("Stack: "); PrintList(Stack); wl;
  wsl("Store: "); PrintStore(Store,0);


  (* Test parsing of nests using folio definition of '[' *)
  NEW(Store); Stack := NIL;

  (* Define '[' *)
  n1 := MakeInteger(ORD('[')); n2 := MakeInstruction(DoParseNest); Join(n1, n2);
  Save(n1);
  Input.l := StringToList("A [nested] test.");
  Parse;
  ws("Stack: "); PrintList(Stack); wl;
  wsl("Store: "); PrintStore(Store,0);

END TestParse;

BEGIN Abort:=FALSE; Stack:=NIL; NEW(Store); NEW(Input); NEW(Output);
  wsl("Folio test.");
  IF SIZE(i64) # 8 THEN
    ws("SIZE(i64) = "); wi(SIZE(i64)); ws(", must be 8."); Fail("")
  END;
  TestAddNode;
  TestExecute;
  TestStore;
  TestSwap;
  TestParse;
END folio.
