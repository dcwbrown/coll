MODULE fol; (* FOL - forthishness on lispishness *)

IMPORT TextWriter, SYSTEM;

CONST

TYPE
  (* Atom = LONGINT; *)  (* Top 4 bits encode type, remainder depend on type *)

  List           = POINTER TO ListDesc;
  LinkedListNode = POINTER TO LinkedListNodeDesc;
  Function       = PROCEDURE();

  Atom = POINTER TO AtomDesc; AtomDesc = RECORD END;
  IntegerAtom   = POINTER TO IntegerAtomDesc;   IntegerAtomDesc   = RECORD(AtomDesc) int:  LONGINT  END;
  CharacterAtom = POINTER TO CharacterAtomDesc; CharacterAtomDesc = RECORD(AtomDesc) char: LONGINT  END; (* Unicode code point *)
  ForkAtom      = POINTER TO ForkAtomDesc;      ForkAtomDesc      = RECORD(AtomDesc) fork: List     END;
  NestAtom      = POINTER TO NestAtomDesc;      NestAtomDesc      = RECORD(AtomDesc) nest: List     END;
  FunctionAtom  = POINTER TO FunctionAtomDesc;  FunctionAtomDesc  = RECORD(AtomDesc) fn:   Function END;

  AtomGetter   = PROCEDURE(l: List): Atom;
  Advancer     = PROCEDURE(l: List; i: LONGINT);
  EOLTest      = PROCEDURE(l: List): BOOLEAN;
  LengthGetter = PROCEDURE(l: List): LONGINT;

  ListHandler = POINTER TO RECORD
    GetAtom:   AtomGetter;
    Advance:   Advancer;
    EOL:       EOLTest;
    GetLength: LengthGetter;
  END;

  ListDesc = RECORD handler: ListHandler END;

  LinkedListNodeDesc = RECORD
    next: LinkedListNode;
    atom: Atom;
  END;

  LinkedList     = POINTER TO LinkedListDesc;
  LinkedListDesc = RECORD(ListDesc)
    first:   LinkedListNode;
    curr:    LinkedListNode
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

  LinkedListHandler: ListHandler;
  ArrayListHandler:  ListHandler;
  ListWalkerHandler: ListHandler;

  Stack: LinkedList;



(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE sl(s: ARRAY OF CHAR): LONGINT; BEGIN RETURN TextWriter.StringLength(s) END sl;

PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)        END ws;
PROCEDURE wc(c: CHAR);           BEGIN TextWriter.Char(c)          END wc;
PROCEDURE wl;                    BEGIN TextWriter.NewLine          END wl;
PROCEDURE wi(i: LONGINT);        BEGIN TextWriter.Integer(i)       END wi;
PROCEDURE wnb;                   BEGIN TextWriter.NoBreak          END wnb;
PROCEDURE wlc;                   BEGIN TextWriter.StartLine        END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN TextWriter.StringNewLine(s) END wsl;


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


(* ---------------------------- Handler shortcuts --------------------------- *)

PROCEDURE GetAtom(l: List): Atom;       BEGIN RETURN l.handler.GetAtom(l)   END GetAtom;
PROCEDURE Advance(l: List; o: LONGINT); BEGIN l.handler.Advance(l, o)       END Advance;
PROCEDURE Rewind(l: List);              BEGIN l.handler.Advance(l, -1)      END Rewind;
PROCEDURE EOL(l: List): BOOLEAN;        BEGIN RETURN l.handler.EOL(l)       END EOL;
PROCEDURE GetLength(l: List): LONGINT;  BEGIN RETURN l.handler.GetLength(l) END GetLength;

PROCEDURE MakeIntegerAtom(i: LONGINT): IntegerAtom;
VAR result: IntegerAtom;
BEGIN NEW(result); result.int := i;
RETURN result END MakeIntegerAtom;

(* -------------------------------- Utility --------------------------------- *)

PROCEDURE ^WriteList(l: List);

PROCEDURE WriteListNode(l: List);
VAR a: Atom;
BEGIN
  a := GetAtom(l);
  WITH
    a: CharacterAtom DO wc(CHR(a.char))
  | a: IntegerAtom   DO ws("N("); wi(a.int); ws(")")
  | a: NestAtom      DO ws("<nest>("); WriteList(a.nest); wc(')');
  | a: ForkAtom      DO ws("<fork>")
  | a: FunctionAtom  DO ws("<function>")
  ELSE                  ws("<Unrecognised>")
  END
END WriteListNode;

PROCEDURE WriteList(l: List);
BEGIN
  Rewind(l);
  IF EOL(l) THEN wsl("<empty>")
  ELSE
    WHILE ~EOL(l) DO WriteListNode(l); Advance(l, 1) END;
    Rewind(l)
  END
END WriteList;


(* ----------------------- Linked list implementation ----------------------- *)

PROCEDURE LinkedListAtomGetter(l: List): Atom;
BEGIN
  Assert(l IS LinkedList, "Expected LinkedList");
  Assert(l(LinkedList).curr # NIL, "Expected non-nil curr in LinkedList");
  RETURN l(LinkedList).curr.atom;
END LinkedListAtomGetter;

PROCEDURE LinkedListAdvancer(l: List; o: LONGINT);
BEGIN
  Assert(l IS LinkedList, "Expected linked list");
  Assert((o > 0) OR (o = -1), "Unexpected offset passed to linked list advancer");
  IF o < 0 THEN
    l(LinkedList).curr := l(LinkedList).first
  ELSE
    WHILE (o > 0) & (l(LinkedList).curr # NIL) DO
      l(LinkedList).curr := l(LinkedList).curr.next;
      DEC(o)
    END
  END
END LinkedListAdvancer;

PROCEDURE LinkedListEOLTest(l: List): BOOLEAN;
BEGIN
  Assert(l IS LinkedList, "Expected LinkedList");
  RETURN l(LinkedList).curr = NIL
END LinkedListEOLTest;

PROCEDURE LinkedListLengthGetter(l: List): LONGINT;
VAR result: LONGINT; p: LinkedListNode;
BEGIN result := 0;  p := l(LinkedList).first;
  WHILE p # NIL DO INC(result); p := p.next END;
RETURN result END LinkedListLengthGetter;

PROCEDURE MakeLinkedList(n: LinkedListNode): LinkedList;
VAR result: LinkedList;
BEGIN
  NEW(result);
  result.handler := LinkedListHandler;
  result.first   := n;
  result.curr    := n;
RETURN result END MakeLinkedList;

PROCEDURE MakeNestAtom(l: List): NestAtom;
VAR result: NestAtom;
BEGIN NEW(result); result.nest := l;
RETURN result END MakeNestAtom;

PROCEDURE LinkedListAddAtom(l: LinkedList; atom: Atom);
VAR node: LinkedListNode;
BEGIN
  NEW(node);
  node.atom := atom;
  node.next := NIL;
  IF l.first = NIL THEN l.first := node; l.curr := node
  ELSE
    Assert(l.curr # NIL, "LinkedListAddAtom expected empty list or list not at end.");
    node.next := l.curr.next;
    l.curr.next := node;
    l.curr := node
  END;
END LinkedListAddAtom;

PROCEDURE MakeText(s: ARRAY OF CHAR): List;
VAR result: LinkedList;  i, l: LONGINT;  ca: CharacterAtom;
BEGIN
  result := MakeLinkedList(NIL);  l := sl(s);
  FOR i := 0 TO l-1 DO NEW(ca); ca.char := ORD(s[i]); LinkedListAddAtom(result, ca) END;
RETURN result END MakeText;


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

PROCEDURE ArrayListEOLTest(l: List): BOOLEAN;
BEGIN
  Assert(l IS ArrayList, "Expected ArrayList");
  RETURN l(ArrayList).curr >= LEN(l(ArrayList).atoms^)
END ArrayListEOLTest;

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

PROCEDURE AtNestStart(l: ListWalker): BOOLEAN;
VAR a: Atom; result: BOOLEAN;
BEGIN result := FALSE;
  IF ~EOL(l.list) THEN a := GetAtom(l.list); result := a IS NestAtom END;
RETURN result END AtNestStart;

PROCEDURE AtNestEnd(l: ListWalker): BOOLEAN;
BEGIN RETURN EOL(l.list) & (l.parent # NIL) END AtNestEnd;

PROCEDURE ResolveNesting(l: ListWalker); (* At nest boundaries steps in or out *)
VAR a: Atom; lw: ListWalker;
BEGIN
  WHILE AtNestStart(l) OR AtNestEnd(l) DO
    IF AtNestStart(l) THEN
      a := GetAtom(l.list); (* Get the nest atom *)
      NEW(lw);  lw^ := l^;
      l.list := a(NestAtom).nest;
      l.parent := lw
    ELSE (* At nest end *)
      l^ := l.parent^;
      Advance(l.list, 1)
    END
  END
END ResolveNesting;

PROCEDURE ListWalkerAtomGetter(l: List): Atom;
BEGIN Assert(l IS ListWalker, "Expected ListWalker");
  ResolveNesting(l(ListWalker));
RETURN GetAtom(l(ListWalker).list) END ListWalkerAtomGetter;

PROCEDURE ListWalkerAdvancer(l: List; o: LONGINT);
VAR lw: ListWalker; a: Atom;
BEGIN
  Assert(l IS ListWalker, "Expected array list");
  Assert((o > 0) OR (o = -1), "Unexpected offset passed to array list advancer");
  IF o < 0 THEN (* Rewind ListWalker *)
    lw := l(ListWalker); WHILE lw.parent # NIL DO lw := lw.parent END;
    l(ListWalker)^ := lw^;
    Advance(l(ListWalker).list, -1)
  ELSE
    (* Advance ListWalker by o elements, skip over nested nodes *)
    Advance(l(ListWalker).list, o);
  END
END ListWalkerAdvancer;

PROCEDURE ListWalkerEOLTest(l: List): BOOLEAN;
BEGIN Assert(l IS ListWalker, "Expected ListWalker");
  ResolveNesting(l(ListWalker));
RETURN (l(ListWalker).parent = NIL) & EOL(l(ListWalker).list) END ListWalkerEOLTest;

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


(* -------------------------------- Parsing --------------------------------- *)

(* Returns nested list (between [ and ]) extracted from imput list. *)
PROCEDURE ParseNestedList(l: LinkedList): LinkedList;
VAR result: LinkedList; depth: LONGINT; a: Atom; ch: LONGINT;
BEGIN
  result := MakeLinkedList(NIL);
  depth := 1;
  WHILE (depth > 0) & ~EOL(l) DO
    a := GetAtom(l);  Assert(a IS CharacterAtom, "ParseNestedList encountered non-character atom.");
    ch := a(CharacterAtom).char;
    CASE ch OF
      ORD('['): INC(depth);
    | ORD(']'): DEC(depth)
    ELSE
    END;
    IF depth > 0 THEN LinkedListAddAtom(result, a) END;
    Advance(l,1)
  END;
RETURN result END ParseNestedList;

PROCEDURE ParseInteger(l: LinkedList): LONGINT;
VAR result: LONGINT; a: Atom; d: LONGINT;
BEGIN
  result := 0;
  WHILE (l # NIL) & ~EOL(l) DO
    a := GetAtom(l); Assert(a IS CharacterAtom, "ParseInteger encountered non-character atom");
    d := a(CharacterAtom).char - ORD('0');
    (*wlc; ws("ParseInteger, digit = "); wi(d); wl;*)
    IF (d < 0) OR (d > 9) THEN l := NIL
    ELSE result := result * 10 + d; Advance(l,1)
    END
  END;
RETURN result; END ParseInteger;

PROCEDURE ParseWord(l: LinkedList): LinkedList;
VAR result: LinkedList; a: Atom; ch: LONGINT;
BEGIN
  result := MakeLinkedList(NIL);
  WHILE (l # NIL) & ~EOL(l) DO
    a := GetAtom(l);
    Assert(a IS CharacterAtom, "Parse encountered non-character atom");
    ch := a(CharacterAtom).char;
    CASE ch OF
      ORD('['), ORD(']'), ORD(' '), 13, 10: l := NIL
    ELSE
      LinkedListAddAtom(result, a);  Advance(l,1);
    END;
  END;
  wlc; ws("Parse word returning: '"); WriteList(result); wsl("'");
RETURN result; END ParseWord;

PROCEDURE Parse(l: LinkedList): List; (* Expect input to be purely a list of characters *)
VAR a: Atom; ch: LONGINT; result: LinkedList;
BEGIN
  result := MakeLinkedList(NIL);
  WHILE ~EOL(l) DO
    a := GetAtom(l); Assert(a IS CharacterAtom, "Parse encountered non-character atom");
    ch := a(CharacterAtom).char;
    CASE ch OF
      ORD('['): Advance(l,1); LinkedListAddAtom(result, MakeNestAtom(ParseNestedList(l)))
    | ORD(' '),13,11:
    | ORD('0')..ORD('9'): LinkedListAddAtom(result, MakeIntegerAtom(ParseInteger(l)))
    ELSE LinkedListAddAtom(result, MakeNestAtom(ParseWord(l)))
    END;
    Advance(l,1);
  END;
RETURN result END Parse;


(* -------------------------------- Testing --------------------------------- *)

PROCEDURE Test;
VAR l1, l2, l3, n1: List; na: NestAtom;
BEGIN
  l1 := MakeText("This is a test.");
  WriteList(l1); wl;

  l2 := MakeArrayList(l1);
  WriteList(l2); wl;

  l3 := MakeListWalker(l1);
  WriteList(l3); wl;

  n1 := MakeText(" nested ");
  Rewind(l1); Advance(l1, 9);
  NEW(na); na.nest := n1;
  l1(LinkedList).curr.atom := na;

  WriteList(l1); wl;

  l3 := MakeListWalker(l1);
  WriteList(l3); wl;

  l1 := MakeText("Alpha 23 beta [gamma delta] epsilon");
  WriteList(l1); wl;

  Rewind(l1); l2 := Parse(l1(LinkedList)); WriteList(l2); wl;

  l3 := MakeListWalker(l2); WriteList(l3); wl;


END Test;

(* ---------------------------- Initialization ------------------------------ *)

BEGIN
  Abort := FALSE;
  Stack := NIL;

  NEW(LinkedListHandler);
  LinkedListHandler.GetAtom   := LinkedListAtomGetter;
  LinkedListHandler.Advance   := LinkedListAdvancer;
  LinkedListHandler.EOL       := LinkedListEOLTest;
  LinkedListHandler.GetLength := LinkedListLengthGetter;

  NEW(ArrayListHandler);
  ArrayListHandler.GetAtom   := ArrayListAtomGetter;
  ArrayListHandler.Advance   := ArrayListAdvancer;
  ArrayListHandler.EOL       := ArrayListEOLTest;
  ArrayListHandler.GetLength := ArrayListLengthGetter;

  NEW(ListWalkerHandler);
  ListWalkerHandler.GetAtom   := ListWalkerAtomGetter;
  ListWalkerHandler.Advance   := ListWalkerAdvancer;
  ListWalkerHandler.EOL       := ListWalkerEOLTest;
  ListWalkerHandler.GetLength := ListWalkerLengthGetter;


  Test
END fol.
