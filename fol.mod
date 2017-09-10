MODULE fol; (* FOL - forthishness on lispishness *)

IMPORT TextWriter, SYSTEM;

CONST

TYPE
  (* Atom = LONGINT; *)  (* Top 4 bits encode type, remainder depend on type *)

  List           = POINTER TO ListDesc;
  LinkedListNode = POINTER TO LinkedListNodeDesc;
  Function       = PROCEDURE();

  Atom = POINTER TO AtomDesc; AtomDesc = RECORD END;
  EndAtom       = POINTER TO EndAtomDesc;       EndAtomDesc       = RECORD(AtomDesc)                END;
  IntegerAtom   = POINTER TO IntegerAtomDesc;   IntegerAtomDesc   = RECORD(AtomDesc) int:  LONGINT  END;
  CharacterAtom = POINTER TO CharacterAtomDesc; CharacterAtomDesc = RECORD(AtomDesc) char: LONGINT  END; (* Unicode code point *)
  ForkAtom      = POINTER TO ForkAtomDesc;      ForkAtomDesc      = RECORD(AtomDesc) fork: List     END;
  NestAtom      = POINTER TO NestAtomDesc;      NestAtomDesc      = RECORD(AtomDesc) nest: List     END;
  FunctionAtom  = POINTER TO FunctionAtomDesc;  FunctionAtomDesc  = RECORD(AtomDesc) fn:   Function END;

  AtomGetter   = PROCEDURE(l: List): Atom;
  Rewinder     = PROCEDURE(l: List);
  Advancer     = PROCEDURE(l: List);

  ListHandler = POINTER TO RECORD
    GetAtom:   AtomGetter;
    Rewind:    Rewinder;
    Advance:   Advancer;
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

  ListEndAtom: EndAtom;

  OpenNestingRepresentationAtom:  CharacterAtom;
  CloseNestingRepresentationAtom: CharacterAtom;

  Stack: LinkedList;



(* ----------------- TextWriter convenience functions ----------------------- *)

PROCEDURE slen(s: ARRAY OF CHAR): LONGINT; BEGIN RETURN TextWriter.StringLength(s) END slen;

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

PROCEDURE GetAtom(l: List): Atom; BEGIN RETURN l.handler.GetAtom(l) END GetAtom;
PROCEDURE Advance(l: List);       BEGIN l.handler.Advance(l)        END Advance;
PROCEDURE Rewind(l: List);        BEGIN l.handler.Rewind(l)         END Rewind;

PROCEDURE EOL(l: List): BOOLEAN;
VAR a: Atom;
BEGIN a := GetAtom(l);
RETURN a IS EndAtom END EOL;

PROCEDURE MakeIntegerAtom(i: LONGINT): IntegerAtom;
VAR result: IntegerAtom;
BEGIN NEW(result); result.int := i;
RETURN result END MakeIntegerAtom;


(* -------------------------------- Utility --------------------------------- *)

PROCEDURE ^WriteList(l: List);

PROCEDURE WriteAtom(a: Atom);
BEGIN
  WITH
    a: CharacterAtom DO wc(CHR(a.char))
  | a: IntegerAtom   DO wi(a.int)
  | a: EndAtom       DO ws("<END>")
  | a: NestAtom      DO ws("<NEST>") (*ws(".[."); WriteList(a.nest); ws(".].")*)
  | a: ForkAtom      DO ws("<FORK>")
  | a: FunctionAtom  DO ws("<FUNCTION>")
  ELSE                  ws("<UNRECOGNISED>")
  END
END WriteAtom;

(* Write list starting at current position *)
PROCEDURE WriteList(l: List);
BEGIN
  IF EOL(l) THEN wsl("<empty>")
  ELSE
    WHILE ~EOL(l) DO WriteAtom(GetAtom(l)); Advance(l) END;
    Rewind(l)
  END
END WriteList;

PROCEDURE MakeNestAtom(l: List): NestAtom;
VAR result: NestAtom;
BEGIN NEW(result); result.nest := l;
RETURN result END MakeNestAtom;


(* ----------------------- Linked list implementation ----------------------- *)

PROCEDURE LinkedListAtomGetter(l: List): Atom;
VAR ll: LinkedList; result: Atom;
BEGIN ll := l(LinkedList); result := ListEndAtom;
  IF l(LinkedList).curr # NIL THEN result := l(LinkedList).curr.atom END;
RETURN result  END LinkedListAtomGetter;

PROCEDURE LinkedListRewinder(l: List);
BEGIN l(LinkedList).curr := l(LinkedList).first
END LinkedListRewinder;

PROCEDURE LinkedListAdvancer(l: List);
BEGIN IF l(LinkedList).curr # NIL THEN l(LinkedList).curr := l(LinkedList).curr.next END
END LinkedListAdvancer;

PROCEDURE MakeLinkedList(n: LinkedListNode): LinkedList;
VAR result: LinkedList;
BEGIN
  NEW(result);
  result.handler := LinkedListHandler;
  result.first   := n;
  result.curr    := n;
RETURN result END MakeLinkedList;

PROCEDURE MakeLinkedListNode(a: Atom): LinkedListNode;
VAR result: LinkedListNode;
BEGIN NEW(result); result.atom := a; result.next := NIL;
RETURN result END MakeLinkedListNode;

PROCEDURE LinkedListPushAtom(l: LinkedList; atom: Atom);
VAR node: LinkedListNode;
BEGIN node := MakeLinkedListNode(atom);
  node.next := l.first;
  l.first := node
END LinkedListPushAtom;

PROCEDURE LinkedListPopAtom(l: LinkedList): Atom;
VAR result: Atom;
BEGIN result := ListEndAtom;
  IF l.first # NIL THEN result := l.first.atom; l.first := l.first.next END;
RETURN result END LinkedListPopAtom;

PROCEDURE LinkedListAddAtom(l: LinkedList; atom: Atom);
VAR node: LinkedListNode;
BEGIN node := MakeLinkedListNode(atom);
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
  result := MakeLinkedList(NIL);  l := slen(s);
  FOR i := 0 TO l-1 DO NEW(ca); ca.char := ORD(s[i]); LinkedListAddAtom(result, ca) END;
RETURN result END MakeText;


(* -----------------------------ArrayList implementation -------------------- *)

PROCEDURE ArrayListAtomGetter(l: List): Atom;
VAR al: ArrayList; result: Atom;
BEGIN al := l(ArrayList); result := ListEndAtom;
  IF al.curr < LEN(al.atoms^) THEN result := al.atoms[al.curr] END;
RETURN result END ArrayListAtomGetter;

PROCEDURE ArrayListRewinder(l: List);
BEGIN l(ArrayList).curr := 0
END ArrayListRewinder;

PROCEDURE ArrayListAdvancer(l: List);
VAR al: ArrayList;
BEGIN al := l(ArrayList);
  IF al.curr < LEN(al.atoms^) THEN INC(al.curr) END
END ArrayListAdvancer;

PROCEDURE MakeArrayList(s: List): ArrayList;
VAR result: ArrayList;  i, l: LONGINT;
BEGIN
  NEW(result);
  result.handler := ArrayListHandler;
  l := 0; Rewind(s); WHILE ~EOL(s) DO Advance(s); INC(l) END;  (* Measure length of s *)
  NEW(result.atoms, l);
  Rewind(s);
  FOR i := 0 TO l-1 DO result.atoms[i] := GetAtom(s); Advance(s) END;
  result.curr := 0;
RETURN result END MakeArrayList;


(* ----------------------------- ListWalker -------------------------------- *)

PROCEDURE ListWalkerAtStartOfNest(l: ListWalker): BOOLEAN;
VAR a: Atom;
BEGIN a := GetAtom(l.list);
RETURN a IS NestAtom END ListWalkerAtStartOfNest;

PROCEDURE ListWalkerAtEndOfNest(l: ListWalker): BOOLEAN;
BEGIN
RETURN EOL(l.list) & (l.parent # NIL) END ListWalkerAtEndOfNest;

PROCEDURE ListWalkerAtomGetter(l: List): Atom;
VAR a: Atom;
BEGIN Assert(l IS ListWalker, "Expected ListWalker");
  a := GetAtom(l(ListWalker).list);
  IF (a IS EndAtom) & (l(ListWalker).parent # NIL) THEN a := CloseNestingRepresentationAtom
  ELSIF a IS NestAtom THEN a := OpenNestingRepresentationAtom
  END;
RETURN a END ListWalkerAtomGetter;

PROCEDURE ListWalkerRewinder(l: List);
VAR lw: ListWalker; a: Atom; eol: BOOLEAN;
BEGIN lw := l(ListWalker);
  WHILE lw.parent # NIL DO lw := lw.parent END;
  l(ListWalker)^ := lw^;
  Rewind(lw.list)
END ListWalkerRewinder;

PROCEDURE ListWalkerAdvancer(l: List);
VAR lw, parent: ListWalker; a: Atom;
BEGIN lw := l(ListWalker);
  a := GetAtom(lw.list);
  IF (a IS EndAtom) & (lw.parent # NIL) THEN
      lw^ := lw.parent^;  Advance(lw.list) (* Advance over NestAtom *)
  ELSIF a IS NestAtom THEN
    NEW(parent);  parent^ := lw^; lw.parent := parent;
    lw.list := a(NestAtom).nest; Rewind(lw.list);
  ELSE
    Advance(lw.list)
  END;
END ListWalkerAdvancer;

PROCEDURE MakeListWalker(l: List): ListWalker;
VAR result: ListWalker;
BEGIN
  NEW(result);
  result.handler := ListWalkerHandler;
  result.list    := l;
RETURN result END MakeListWalker;


(* ------------------------------- Evaluator -------------------------------- *)

PROCEDURE Evaluate(l: List);
VAR a: Atom;
BEGIN
  a := GetAtom(l);
  WHILE ~(a IS EndAtom) DO
    WITH a: FunctionAtom DO a.fn
    ELSE LinkedListPushAtom(Stack, a) END;
    Advance(l); a := GetAtom(l)
  END
END Evaluate;

PROCEDURE MakeIntrinsic(fn: Function): Atom;
VAR result: FunctionAtom;
BEGIN NEW(result); result.fn := fn;
RETURN result END MakeIntrinsic;


(* ------------------------------ Intrinsics -------------------------------- *)

PROCEDURE IntrinsicTest();
BEGIN wlc; wsl("** Intrinsic test evaluated **")
END IntrinsicTest;

PROCEDURE IntrinsicWL();
BEGIN wl
END IntrinsicWL;

PROCEDURE IntrinsicPrint();
VAR a: Atom;
BEGIN a := LinkedListPopAtom(Stack); WriteAtom(a)
END IntrinsicPrint;


(* ------------------------------ Prefix tree ------------------------------- *)

PROCEDURE EqualAtoms(a1, a2: Atom): BOOLEAN;
VAR result: BOOLEAN;
BEGIN result := FALSE;
  WITH
    a1: CharacterAtom DO WITH a2: CharacterAtom DO result := a1.char = a2.char ELSE END
  | a1: IntegerAtom   DO WITH a2: IntegerAtom   DO result := a1.int  = a2.int  ELSE END
  | a1: FunctionAtom  DO WITH a2: FunctionAtom  DO result := a1.fn   = a2.fn   ELSE END
  ELSE END;
RETURN result END EqualAtoms;

(* Advance lists over matching region *)
PROCEDURE MatchLists(l1, l2: List): BOOLEAN;
VAR result: BOOLEAN;
BEGIN result := FALSE;
  WHILE EqualAtoms(GetAtom(l1), GetAtom(l2)) DO
    result := TRUE; Advance(l1); Advance(l2);
  END;
RETURN result END MatchLists;

(* Assumption: at a fork the 2 choices must be differing atoms. *)
PROCEDURE MatchForkedLists(l1, l2: ListWalker): BOOLEAN;
VAR lw1, lw2: ListWalker; a1, a2: Atom; result: BOOLEAN;
BEGIN
  result := MatchLists(l1, l2);
  (* If there's a fork choose which path to take *)
  a1 := GetAtom(l1);  a2 := GetAtom(l2);
  IF a1 IS ForkAtom THEN
    wsl("Recurse - try fork.");
    lw1 := MakeListWalker(a1(ForkAtom).fork); Rewind(lw1); (* Try alternate first *)
    IF MatchForkedLists(lw1, l2) THEN
      wsl("Fork taken");
      l1^ := lw1^; result := TRUE
    ELSE (* alternate fork didn't match, so skip nest atom *)
      wsl("Fork not taken");
      Advance(l1.list);
      wsl("Recurse - try next.");
      IF MatchForkedLists(l1, l2) THEN
        l1^ := lw1^; result := TRUE
      END
    END
  ELSIF a2 IS ForkAtom THEN
    result := result OR MatchForkedLists(l2, l1)
  END;
RETURN result END MatchForkedLists;

(* -------------------------------- Parsing --------------------------------- *)

(* Returns nested list (between [ and ]) extracted from input list. *)
PROCEDURE ParseNestedList(l: LinkedList): LinkedList;
VAR result: LinkedList; depth: LONGINT; a: Atom; ch: LONGINT;
BEGIN result := MakeLinkedList(NIL); depth := 1;
  WHILE (depth > 0) & ~EOL(l) DO
    a := GetAtom(l);  Assert(a IS CharacterAtom, "ParseNestedList encountered non-character atom.");
    ch := a(CharacterAtom).char;
    IF ch = ORD('[') THEN INC(depth) ELSIF ch = ORD(']') THEN DEC(depth) END;
    IF depth > 0 THEN LinkedListAddAtom(result, a) END;
    Advance(l)
  END;
RETURN result END ParseNestedList;

PROCEDURE ParseInteger(l: LinkedList): LONGINT;
VAR result: LONGINT; a: Atom; d: LONGINT;
BEGIN
  result := 0;
  WHILE (l # NIL) & ~EOL(l) DO a := GetAtom(l);
    WITH a: CharacterAtom DO
      d := a.char - ORD('0');
      IF (d >= 0) & (d <= 9) THEN result := result * 10 + d; Advance(l)
      ELSE l := NIL END
    ELSE l := NIL END
  END;
RETURN result END ParseInteger;

PROCEDURE ParseWord(l: LinkedList): LinkedList;
VAR result: LinkedList; a: Atom; ch: LONGINT;
BEGIN
  result := MakeLinkedList(NIL);
  WHILE (l # NIL) & ~EOL(l) DO a := GetAtom(l);
    Assert(a IS CharacterAtom, "Parse encountered non-character atom");
    WITH a: CharacterAtom DO
      CASE a.char OF
        ORD('['), ORD(']'), ORD(' '), 13, 10: l := NIL
      ELSE LinkedListAddAtom(result, a); Advance(l); END
    ELSE l := NIL END
  END;
RETURN result END ParseWord;

PROCEDURE Parse(l: LinkedList): List; (* Expect input to be purely a list of characters *)
VAR a: Atom; ch: LONGINT; result: LinkedList;
BEGIN
  result := MakeLinkedList(NIL);
  WHILE ~EOL(l) DO
    a := GetAtom(l); Assert(a IS CharacterAtom, "Parse encountered non-character atom");
    ch := a(CharacterAtom).char;
    CASE ch OF
      ORD('['): Advance(l); LinkedListAddAtom(result, MakeNestAtom(ParseNestedList(l)))
    | ORD(' '),13,11:
    | ORD('0')..ORD('9'): LinkedListAddAtom(result, MakeIntegerAtom(ParseInteger(l)))
    ELSE LinkedListAddAtom(result, MakeNestAtom(ParseWord(l)))
    END;
    Advance(l);
  END;
RETURN result END Parse;


(* -------------------------------- Testing --------------------------------- *)

PROCEDURE Test;
VAR l1, l2, l3, n1: List; na: NestAtom; fa: ForkAtom;
    i: INTEGER; match: BOOLEAN;
BEGIN
  l1 := MakeText("This is a test.");
  Rewind(l1); WriteList(l1); wl;

  l2 := MakeArrayList(l1);
  Rewind(l2); WriteList(l2); wl;

  l3 := MakeListWalker(l1);
  Rewind(l3); WriteList(l3); wl;

  n1 := MakeText(" nested ");
  Rewind(l1); FOR i := 1 TO 9 DO Advance(l1) END;
  NEW(na); na.nest := n1;
  l1(LinkedList).curr.atom := na;

  Rewind(l1); WriteList(l1); wl;

  l3 := MakeListWalker(l1);
  Rewind(l3); WriteList(l3); wl;

  l1 := MakeText("Alpha 23 beta [gamma delta] epsilon");
  Rewind(l1); WriteList(l1); wl;

  Rewind(l1); l2 := Parse(l1(LinkedList)); Rewind(l2); WriteList(l2); wl;

  l3 := MakeListWalker(l2); Rewind(l3); WriteList(l3); wl;


  l1 := MakeListWalker(MakeText("This is a test."));      Rewind(l1);
  l2 := MakeListWalker(MakeText("This is not a test."));  Rewind(l2);

  match := MatchForkedLists(l1(ListWalker),l2(ListWalker));
  ws("MatchForkedLists");
  IF ~match THEN wsl("failed.")
  ELSE
    wsl("succeeded:");
    ws("  l1 ends: "); WriteList(l1); wl;
    ws("  l2 ends: "); WriteList(l2); wl;
  END;


  l1 := MakeText("This is a test.");
  Rewind(l1); FOR i := 1 TO 7 DO Advance(l1) END;
  NEW(fa);  fa.fork := MakeText("not a test.");
  LinkedListAddAtom(l1(LinkedList), fa);

  l1 := MakeListWalker(l1); Rewind(l1);
  l2 := MakeListWalker(MakeText("This is not."));  Rewind(l2);

  match := (*MatchLists*)MatchForkedLists(l1(ListWalker),l2(ListWalker));
  ws("MatchForkedLists");
  IF ~match THEN wsl("failed.")
  ELSE
    wsl("succeeded:");
    ws("  l1 ends: "); WriteList(l1); wl;
    ws("  l2 ends: "); WriteList(l2); wl;
  END;


  l1 := MakeText("This is not a test.");
  Rewind(l1); FOR i := 1 TO 7 DO Advance(l1) END;
  NEW(fa);  fa.fork := MakeText("a test.");
  LinkedListAddAtom(l1(LinkedList), fa);

  l1 := MakeListWalker(l1); Rewind(l1);
  l2 := MakeListWalker(MakeText("This is not."));  Rewind(l2);

  match := (*MatchLists*)MatchForkedLists(l1(ListWalker),l2(ListWalker));
  ws("MatchForkedLists");
  IF ~match THEN wsl("failed.")
  ELSE
    wsl("succeeded:");
    ws("  l1 ends: "); WriteList(l1); wl;
    ws("  l2 ends: "); WriteList(l2); wl;
  END;

  l1 := MakeLinkedList(NIL);
  LinkedListAddAtom(l1(LinkedList), MakeIntrinsic(IntrinsicTest));
  LinkedListAddAtom(l1(LinkedList), MakeIntegerAtom(1234));
  LinkedListAddAtom(l1(LinkedList), MakeIntrinsic(IntrinsicPrint));
  LinkedListAddAtom(l1(LinkedList), MakeIntrinsic(IntrinsicWL));
  Rewind(l1); Evaluate(l1);

END Test;

(* ---------------------------- Initialization ------------------------------ *)

BEGIN
  Abort := FALSE;
  Stack := MakeLinkedList(NIL);

  NEW(LinkedListHandler);
  LinkedListHandler.GetAtom := LinkedListAtomGetter;
  LinkedListHandler.Rewind  := LinkedListRewinder;
  LinkedListHandler.Advance := LinkedListAdvancer;

  NEW(ArrayListHandler);
  ArrayListHandler.GetAtom := ArrayListAtomGetter;
  ArrayListHandler.Rewind  := ArrayListRewinder;
  ArrayListHandler.Advance := ArrayListAdvancer;

  NEW(ListWalkerHandler);
  ListWalkerHandler.GetAtom := ListWalkerAtomGetter;
  ListWalkerHandler.Rewind  := ListWalkerRewinder;
  ListWalkerHandler.Advance := ListWalkerAdvancer;

  NEW(ListEndAtom);

  NEW(OpenNestingRepresentationAtom);  OpenNestingRepresentationAtom.char  := ORD('[');
  NEW(CloseNestingRepresentationAtom); CloseNestingRepresentationAtom.char := ORD(']');


  Test
END fol.
