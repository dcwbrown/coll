MODULE fol; (* FOL - forthishness on lispishness *)

IMPORT TextWriter, SYSTEM;

CONST
  (* List element kinds *)
  Integer   = 0;
  Character = 1;
  Fork      = 2;
  Nest      = 3;
  Function  = 4;

TYPE
  Atom = LONGINT;  (* Top 4 bits encode type, remainder depend on type *)

  List = POINTER TO ListDesc;

  AtomGetter   = PROCEDURE(l: List): Atom;
  Advancer     = PROCEDURE(l: List; i: LONGINT);
  EndedTest    = PROCEDURE(l: List): BOOLEAN;
  LengthGetter = PROCEDURE(l: List): LONGINT;

  ListHandler = POINTER TO RECORD
    GetAtom:   AtomGetter;
    Advance:   Advancer;
    Ended:     EndedTest;
    GetLength: LengthGetter;
  END;

  ListDesc = RECORD handler: ListHandler END;

  LinkedListNode = RECORD
    next: LONGINT;
    atom: Atom;
  END;

  LinkedList     = POINTER TO LinkedListDesc;
  LinkedListDesc = RECORD(ListDesc)
    first:   LONGINT;
    curr:    LONGINT
  END;

  ArrayList     = POINTER TO ArrayListDesc;
  ArrayListDesc = RECORD(ListDesc)
    atoms:   POINTER TO ARRAY OF Atom;
    curr:    LONGINT
  END;

  ListWalker     = POINTER TO ListWalkerDesc;
  ListWalkerDesc = RECORD(ListDesc)
    list:   List;
    parent: ListWalker
  END;



VAR
  (*Names: INTEGER;*)  (* Root LinkedListNode of name table *)
  Abort: BOOLEAN;
  Nodes: ARRAY 10000 OF LinkedListNode;
  Free:  LONGINT;

  LinkedListHandler: ListHandler;
  ArrayListHandler:  ListHandler;
  ListWalkerHandler: ListHandler;



(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE sl(s: ARRAY OF CHAR): LONGINT; BEGIN RETURN TextWriter.StringLength(s) END sl;

PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)              END ws;
PROCEDURE wc(c: CHAR);           BEGIN TextWriter.Char(c)                END wc;
PROCEDURE wl;                    BEGIN TextWriter.NewLine                END wl;
PROCEDURE wi(i: LONGINT);        BEGIN TextWriter.Integer(i)             END wi;
PROCEDURE wnb;                   BEGIN TextWriter.NoBreak                END wnb;
PROCEDURE wlc;                   BEGIN TextWriter.StartLine              END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN TextWriter.StringNewLine(s)       END wsl;


(* ------------ Error handling convenience functions --------------- *)

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Internal error:"); wsl(msg); HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* -------------------------- Linked list node allocation ------------------- *)

PROCEDURE NewNode(VAR node: LONGINT);
BEGIN
  Assert(Free < LEN(Nodes), "No more free nodes.");
  node := Free;
  INC(Free)
END NewNode;


(* -------------------------------- Atoms --------------------------------- *)

PROCEDURE MakeAtom(type: LONGINT; value: LONGINT): Atom;
BEGIN RETURN SYSTEM.LSH(SYSTEM.LSH(value, 4), -4)
           + SYSTEM.ROT(type MOD 16, -4);
END MakeAtom;

PROCEDURE ExtractType(v: Atom): INTEGER;
BEGIN RETURN SYSTEM.VAL(INTEGER, SYSTEM.ROT(v, 4) MOD 16) END ExtractType;

PROCEDURE ExtractValue(v: Atom): LONGINT;
BEGIN RETURN ASH(SYSTEM.ROT(v, 4), -4) END ExtractValue;


(* ---------------------------- Handler shortcuts --------------------------- *)

PROCEDURE GetAtom(l: List): Atom;       BEGIN RETURN l.handler.GetAtom(l)     END GetAtom;
PROCEDURE GetType(l: List): INTEGER;    BEGIN RETURN ExtractType(GetAtom(l))  END GetType;
PROCEDURE GetValue(l: List): LONGINT;   BEGIN RETURN ExtractValue(GetAtom(l)) END GetValue;
PROCEDURE Advance(l: List; o: LONGINT); BEGIN l.handler.Advance(l, o)         END Advance;
PROCEDURE Rewind(l: List);              BEGIN l.handler.Advance(l, -1)        END Rewind;
PROCEDURE Ended(l: List): BOOLEAN;      BEGIN RETURN l.handler.Ended(l)       END Ended;
PROCEDURE GetLength(l: List): LONGINT;  BEGIN RETURN l.handler.GetLength(l)   END GetLength;


(* ----------------------- Linked list implementation ----------------------- *)

PROCEDURE LinkedListAtomGetter(l: List): Atom;
BEGIN
  Assert(l IS LinkedList, "Expected LinkedList");
  Assert(l(LinkedList).curr # 0, "Expected non-nil curr in LinkedList");
  RETURN Nodes[l(LinkedList).curr].atom;
END LinkedListAtomGetter;

PROCEDURE LinkedListAdvancer(l: List; o: LONGINT);
BEGIN
  Assert(l IS LinkedList, "Expected linked list");
  Assert((o > 0) OR (o = -1), "Unexpected offset passed to linked list advancer");
  IF o < 0 THEN
    l(LinkedList).curr := l(LinkedList).first
  ELSE
    WHILE o > 0 DO
      Assert(l(LinkedList).curr # 0, "Expected non-nil curr in LinkedList");
      l(LinkedList).curr := Nodes[l(LinkedList).curr].next;
      DEC(o)
    END
  END
END LinkedListAdvancer;

PROCEDURE LinkedListEndedTest(l: List): BOOLEAN;
BEGIN
  Assert(l IS LinkedList, "Expected LinkedList");
  RETURN l(LinkedList).curr = 0
END LinkedListEndedTest;

PROCEDURE LinkedListLengthGetter(l: List): LONGINT;
VAR result, p: LONGINT;
BEGIN result := 0;  p := l(LinkedList).first;
  WHILE p # 0 DO INC(result); p := Nodes[p].next END;
RETURN result END LinkedListLengthGetter;

PROCEDURE MakeEmptyLinkedList(): LinkedList;
VAR result: LinkedList;
BEGIN
  NEW(result);
  result.handler := LinkedListHandler;
  result.first   := 0;
  result.curr    := 0;
RETURN result END MakeEmptyLinkedList;

PROCEDURE LinkedListAddAtom(l: LinkedList; atom: Atom);
VAR node: LONGINT;
BEGIN
  NewNode(node);
  Nodes[node].atom := atom;
  Nodes[node].next := 0;
  IF l.first = 0 THEN l.first := node; l.curr := node
  ELSE
    Assert(l.curr # 0, "LinkedListAddAtom expected empty list or list not at end.");
    Nodes[node].next := Nodes[l.curr].next;
    Nodes[l.curr].next := node;
    l.curr := node
  END;
END LinkedListAddAtom;


(* -----------------------------ArrayList implementation -------------------- *)

PROCEDURE ArrayListAtomGetter(l: List): Atom;
BEGIN Assert(l IS ArrayList, "Expected ArrayList");
RETURN l(ArrayList).atoms[l(ArrayList).curr] END ArrayListAtomGetter;

PROCEDURE ArrayListAdvancer(l: List; o: LONGINT);
BEGIN
  Assert(l IS ArrayList, "Expected array list");
  Assert((o > 0) OR (o = -1), "Unexpected offset passed to array list advancer");
  IF o < 0 THEN
    l(ArrayList).curr := 0
  ELSIF l(ArrayList).curr + o < LEN(l(ArrayList).atoms^) THEN
    INC(l(ArrayList).curr, o)
  ELSE
    l(ArrayList).curr := LEN(l(ArrayList).atoms^)
  END
END ArrayListAdvancer;

PROCEDURE ArrayListEndedTest(l: List): BOOLEAN;
BEGIN
  Assert(l IS ArrayList, "Expected ArrayList");
  RETURN l(ArrayList).curr >= LEN(l(ArrayList).atoms^)
END ArrayListEndedTest;

PROCEDURE ArrayListLengthGetter(l: List): LONGINT;
BEGIN
IF l(ArrayList).atoms = NIL THEN RETURN 0
ELSE RETURN LEN(l(ArrayList).atoms^) END
END ArrayListLengthGetter;

PROCEDURE MakeArrayList(s: List): ArrayList;
VAR result: ArrayList;  i, l: LONGINT;
BEGIN
  NEW(result);
  result.handler := ArrayListHandler;

  i := 0;  l := GetLength(s);
  NEW(result.atoms, l);
  Advance(s, -1);
  FOR i := 0 TO l-1 DO
    result.atoms[i] := GetAtom(s);
    Advance(s, 1)
  END;
  result.curr := 0;
RETURN result END MakeArrayList;


(* ----------------------------- ListWalker -------------------------------- *)

PROCEDURE ListWalkerAtomGetter(l: List): Atom;
BEGIN Assert(l IS ListWalker, "Expected ListWalker");
RETURN GetAtom(l(ListWalker).list) END ListWalkerAtomGetter;

PROCEDURE ListWalkerAdvancer(l: List; o: LONGINT);
VAR lw: ListWalker; ll: LinkedList;
BEGIN
  Assert(l IS ListWalker, "Expected array list");
  Assert((o > 0) OR (o = -1), "Unexpected offset passed to array list advancer");
  IF o < 0 THEN (* Rewind ListWalker *)
    lw := l(ListWalker); WHILE lw.parent # NIL DO lw := lw.parent END;
    l(ListWalker)^ := lw^;
    Advance(l(ListWalker).list, -1)
  ELSE
    (* Advance ListWalker by o elements, walking into nested nodes *)
    Advance(l(ListWalker).list, o);
    (* Handle nest or unnest needed *)
    IF Ended(l(ListWalker).list) THEN
        IF l(ListWalker).parent # NIL THEN
          l(ListWalker)^ := l(ListWalker).parent^; Advance(l(ListWalker).list, 1)
        END
    ELSIF GetType(l(ListWalker).list) = Nest THEN
      NEW(lw);
      lw^ := l(ListWalker)^;

      ll := MakeEmptyLinkedList();
      ll.first := GetValue(l(ListWalker).list);
      ll.curr := ll.first;

      l(ListWalker).list := ll;
      l(ListWalker).parent := lw;
    END
  END
END ListWalkerAdvancer;

PROCEDURE ListWalkerEndedTest(l: List): BOOLEAN;
BEGIN Assert(l IS ListWalker, "Expected ListWalker");
RETURN (l(ListWalker).parent = NIL) & Ended(l(ListWalker).list) END ListWalkerEndedTest;

PROCEDURE ListWalkerLengthGetter(l: List): LONGINT;
BEGIN
RETURN GetLength(l(ListWalker).list) END ListWalkerLengthGetter;

PROCEDURE MakeListWalker(l: List): ListWalker;
VAR result: ListWalker;
BEGIN
  NEW(result);
  result.handler := ListWalkerHandler;
  result.list    := l;
RETURN result END MakeListWalker;


(* -------------------------------- Utility --------------------------------- *)

PROCEDURE WriteListNode(l: List);
VAR t: INTEGER; v: LONGINT;
BEGIN
  t := GetType(l);  v := GetValue(l);
  (*ws("WriteListNode, t"); wi(t); ws(", v"); wi(v); wl;*)
  CASE t OF
    Character: wc(CHR(v))
  | Integer:   ws("N-"); wi(v); ws(".");
  | Nest:      ws("<nest>")
  | Fork:      ws("<fork>")
  ELSE         ws("<Unrecognised>")
  END
END WriteListNode;

PROCEDURE MakeText(s: ARRAY OF CHAR): List;
VAR result: LinkedList;  i, l: LONGINT;
BEGIN
  result := MakeEmptyLinkedList();  l := sl(s);
  FOR i := 0 TO l-1 DO LinkedListAddAtom(result, MakeAtom(Character, ORD(s[i]))) END;
RETURN result END MakeText;

PROCEDURE WriteList(l: List);
BEGIN
  Rewind(l);
  IF Ended(l) THEN wsl("<empty>")
  ELSE
    WHILE ~Ended(l) DO WriteListNode(l); Advance(l, 1) END;
    Rewind(l)
  END
END WriteList;


(* -------------------------------- Testing --------------------------------- *)

PROCEDURE Test;
VAR l1, l2, l3, n1: List;
BEGIN
  l1 := MakeText("This is a test.");
  WriteList(l1); wl;

  l2 := MakeArrayList(l1);
  WriteList(l2); wl;

  l3 := MakeListWalker(l1);
  WriteList(l3); wl;

  n1 := MakeText(" nested ");
  Rewind(l1); Advance(l1, 9);
  Nodes[l1(LinkedList).curr].atom := MakeAtom(Nest, n1(LinkedList).first);

  WriteList(l1); wl;

  l3 := MakeListWalker(l1);
  WriteList(l3); wl;

END Test;

(* ---------------------------- Initialization ------------------------------ *)

BEGIN
  Abort := FALSE;
  Free  := 1;   (* Skip node 0 - it's reserved for nil *)
  Nodes[0].next := 0;
  Nodes[0].atom := MakeAtom(-1, -1);

  NEW(LinkedListHandler);
  LinkedListHandler.GetAtom   := LinkedListAtomGetter;
  LinkedListHandler.Advance   := LinkedListAdvancer;
  LinkedListHandler.Ended     := LinkedListEndedTest;
  LinkedListHandler.GetLength := LinkedListLengthGetter;

  NEW(ArrayListHandler);
  ArrayListHandler.GetAtom   := ArrayListAtomGetter;
  ArrayListHandler.Advance   := ArrayListAdvancer;
  ArrayListHandler.Ended     := ArrayListEndedTest;
  ArrayListHandler.GetLength := ArrayListLengthGetter;

  NEW(ListWalkerHandler);
  ListWalkerHandler.GetAtom   := ListWalkerAtomGetter;
  ListWalkerHandler.Advance   := ListWalkerAdvancer;
  ListWalkerHandler.Ended     := ListWalkerEndedTest;
  ListWalkerHandler.GetLength := ListWalkerLengthGetter;


  Test
END fol.
