MODULE fol; (* FOL - forthishness on lispishness *)

IMPORT TextWriter, SYSTEM;

CONST

TYPE
  (* Atom = LONGINT; *)  (* Top 4 bits encode type, remainder depend on type *)

  List           = POINTER TO ListDesc;
  LinkedListNode = POINTER TO LinkedListNodeDesc;
  Function       = PROCEDURE(): List;

  Atom = POINTER TO AtomDesc; AtomDesc = RECORD END;
  EndAtom       = POINTER TO EndAtomDesc;       EndAtomDesc       = RECORD(AtomDesc)                END;
  IntegerAtom   = POINTER TO IntegerAtomDesc;   IntegerAtomDesc   = RECORD(AtomDesc) int:  LONGINT  END;
  CharacterAtom = POINTER TO CharacterAtomDesc; CharacterAtomDesc = RECORD(AtomDesc) char: LONGINT  END; (* Unicode code point *)
  LinkAtom      = POINTER TO LinkAtomDesc;      LinkAtomDesc      = RECORD(AtomDesc) link: List     END;
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

  IotaFunctionList = POINTER TO IotaFunctionListDesc;
  IotaFunctionListDesc = RECORD (ListDesc)
    curr, limit: LONGINT
  END;

  MultiplyFunctionList = POINTER TO MultiplyFunctionListDesc;
  MultiplyFunctionListDesc = RECORD (ListDesc)
    l1, l2: List;
    l1ended, l2ended: BOOLEAN;
  END;

  SingletonAtomList = POINTER TO SingletonAtomListDesc;
  SingletonAtomListDesc = RECORD (ListDesc)
    a: Atom; atend: BOOLEAN
  END;



VAR
  (*Names: INTEGER;*)  (* Root LinkedListNode of name table *)
  Abort: BOOLEAN;

  SingletonAtomListHandler: ListHandler;
  LinkedListHandler:        ListHandler;
  ArrayListHandler:         ListHandler;
  ListWalkerHandler:        ListHandler;
  IotaFunctionHandler:      ListHandler;
  MultiplyFunctionHandler:  ListHandler;

  ListEndAtom: EndAtom;

  OpenNestingRepresentationAtom:  CharacterAtom;
  CloseNestingRepresentationAtom: CharacterAtom;

  Stack: LinkedList;

  EmptyList: LinkedList;


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

PROCEDURE WriteAtom(a: Atom);
BEGIN
  WITH
    a: CharacterAtom DO wc(CHR(a.char))
  | a: IntegerAtom   DO wi(a.int)
  | a: EndAtom       DO ws("<END>")
  | a: LinkAtom      DO ws("<link>") (*ws(".[."); WriteList(a.link); ws(".].")*)
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

PROCEDURE MakeLinkAtom(l: List): LinkAtom;
VAR result: LinkAtom;
BEGIN NEW(result); result.link := l;
RETURN result END MakeLinkAtom;

PROCEDURE AtomAsInt(a: Atom): LONGINT;
BEGIN
RETURN a(IntegerAtom).int END AtomAsInt;


(* ------------------- SingletonAtom list implementation -------------------- *)

PROCEDURE SingletonAtomListAtomGetter(l: List): Atom;
VAR sal: SingletonAtomList; result: Atom;
BEGIN sal := l(SingletonAtomList); result := ListEndAtom;
  IF ~sal.atend THEN result := sal.a END;
RETURN result  END SingletonAtomListAtomGetter;

PROCEDURE SingletonAtomListRewinder(l: List);
BEGIN l(SingletonAtomList).atend := FALSE
END SingletonAtomListRewinder;

PROCEDURE SingletonAtomListAdvancer(l: List);
BEGIN l(SingletonAtomList).atend := TRUE
END SingletonAtomListAdvancer;

PROCEDURE AtomAsList(a: Atom): List;
VAR result: List; sal: SingletonAtomList;
BEGIN
  IF a IS LinkAtom THEN
    result := a(LinkAtom).link
  ELSE
    NEW(sal); sal.handler := SingletonAtomListHandler;
    sal.a := a; sal.atend := FALSE;
    result := sal
  END;
RETURN result END AtomAsList;

(* ----------------------- Linked list implementation ----------------------- *)

PROCEDURE LinkedListAtomGetter(l: List): Atom;
VAR ll: LinkedList; result: Atom;
BEGIN ll := l(LinkedList); result := ListEndAtom;
  IF ll.curr # NIL THEN result := ll.curr.atom END;
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

PROCEDURE ListWalkerAtomGetter(l: List): Atom;
VAR a: Atom;
BEGIN Assert(l IS ListWalker, "Expected ListWalker");
  a := GetAtom(l(ListWalker).list);
  IF (a IS EndAtom) & (l(ListWalker).parent # NIL) THEN a := CloseNestingRepresentationAtom
  ELSIF a IS LinkAtom THEN a := OpenNestingRepresentationAtom
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
      lw^ := lw.parent^;  Advance(lw.list) (* Advance over LinkAtom *)
  ELSIF a IS LinkAtom THEN
    NEW(parent);  parent^ := lw^; lw.parent := parent;
    lw.list := a(LinkAtom).link; Rewind(lw.list);
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
    IF a IS FunctionAtom THEN a := MakeLinkAtom(a(FunctionAtom).fn()) END;
    LinkedListPushAtom(Stack, a); Advance(l); a := GetAtom(l)
  END
END Evaluate;

PROCEDURE MakeIntrinsic(fn: Function): Atom;
VAR result: FunctionAtom;
BEGIN NEW(result); result.fn := fn;
RETURN result END MakeIntrinsic;


(* ------------------------------ Intrinsics -------------------------------- *)

PROCEDURE IntrinsicTest(): List;
BEGIN wlc; wsl("** Intrinsic test evaluated **");
RETURN EmptyList END IntrinsicTest;

PROCEDURE IntrinsicWL(): List;
BEGIN wl;
RETURN EmptyList END IntrinsicWL;

PROCEDURE IntrinsicPrintAtom(): List;
VAR a: Atom;
BEGIN a := LinkedListPopAtom(Stack); WriteAtom(a);
RETURN EmptyList END IntrinsicPrintAtom;

PROCEDURE IntrinsicPrintList(): List;
VAR a: Atom;
BEGIN a := LinkedListPopAtom(Stack); WriteList(a(LinkAtom).link);
RETURN EmptyList END IntrinsicPrintList;


(* -------------------------- Intrinsic Iota -------------------------------- *)

PROCEDURE IotaFunctionAtomGetter(l: List): Atom;
VAR ifl: IotaFunctionList; result: Atom;
BEGIN ifl := l(IotaFunctionList); result := ListEndAtom;
  IF ifl.curr < ifl.limit THEN result := MakeIntegerAtom(ifl.curr) END;
RETURN result END IotaFunctionAtomGetter;

PROCEDURE IotaFunctionRewinder(l: List);
BEGIN l(IotaFunctionList).curr := 0 END IotaFunctionRewinder;

PROCEDURE IotaFunctionAdvancer(l: List);
VAR ifl: IotaFunctionList;
BEGIN ifl := l(IotaFunctionList);
  IF ifl.curr < ifl.limit THEN INC(ifl.curr) END
END IotaFunctionAdvancer;

PROCEDURE IntrinsicIota(): List;
VAR limit: LONGINT; result: IotaFunctionList;
BEGIN limit := AtomAsInt(LinkedListPopAtom(Stack));
  NEW(result); result.handler := IotaFunctionHandler;
  result.curr := 0; result.limit := limit;
RETURN result END IntrinsicIota;


(* ------------------------ Intrinsic Multiply ------------------------------ *)

PROCEDURE MultiplyFunctionAtomGetter(l: List): Atom;
VAR mfl: MultiplyFunctionList; a1, a2, result: Atom;
BEGIN mfl := l(MultiplyFunctionList); result := ListEndAtom;
  a1 := GetAtom(mfl.l1); a2 := GetAtom(mfl.l2);
  IF ~((a1 IS EndAtom) OR (a2 IS EndAtom)) THEN
    result := MakeIntegerAtom(AtomAsInt(a1) * AtomAsInt(a2))
  END;
RETURN result END MultiplyFunctionAtomGetter;

PROCEDURE MultiplyFunctionRewinder(l: List);
VAR mfl: MultiplyFunctionList;
BEGIN mfl := l(MultiplyFunctionList);
  Rewind(mfl.l1);  Rewind(mfl.l2);
  mfl.l1ended := FALSE;  mfl.l2ended := FALSE
END MultiplyFunctionRewinder;

PROCEDURE MultiplyFunctionAdvancer(l: List);
VAR mfl: MultiplyFunctionList; a1, a2: Atom;
BEGIN mfl := l(MultiplyFunctionList);
  Advance(mfl.l1); a1 := GetAtom(mfl.l1); mfl.l1ended := mfl.l1ended OR (a1 IS EndAtom);
  Advance(mfl.l2); a2 := GetAtom(mfl.l2); mfl.l2ended := mfl.l2ended OR (a2 IS EndAtom);
  IF (a1 IS EndAtom) & ~mfl.l2ended THEN Rewind(mfl.l1) END;
  IF (a2 IS EndAtom) & ~mfl.l1ended THEN Rewind(mfl.l2) END;
END MultiplyFunctionAdvancer;

PROCEDURE IntrinsicMultiply(): List;
VAR result: MultiplyFunctionList;
BEGIN
  NEW(result); result.handler := MultiplyFunctionHandler;
  result.l1ended := FALSE;  result.l2ended := FALSE;
  result.l2 := AtomAsList(LinkedListPopAtom(Stack));
  result.l1 := AtomAsList(LinkedListPopAtom(Stack));
RETURN result END IntrinsicMultiply;


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

(* Assumption: at a link the 2 choices must be differing atoms. *)
PROCEDURE MatchForkedLists(l1, l2: ListWalker): BOOLEAN;
VAR lw1, lw2: ListWalker; a1, a2: Atom; result: BOOLEAN;
BEGIN
  result := MatchLists(l1, l2);
  (* If there's a link choose which path to take *)
  a1 := GetAtom(l1);  a2 := GetAtom(l2);
  IF a1 IS LinkAtom THEN
    wsl("Recurse - try link.");
    lw1 := MakeListWalker(a1(LinkAtom).link); Rewind(lw1); (* Try alternate first *)
    IF MatchForkedLists(lw1, l2) THEN
      wsl("link taken");
      l1^ := lw1^; result := TRUE
    ELSE (* alternate link didn't match, so skip link atom *)
      wsl("link not taken");
      Advance(l1.list);
      wsl("Recurse - try next.");
      IF MatchForkedLists(l1, l2) THEN
        l1^ := lw1^; result := TRUE
      END
    END
  ELSIF a2 IS LinkAtom THEN
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
      ORD('['): Advance(l); LinkedListAddAtom(result, MakeLinkAtom(ParseNestedList(l)))
    | ORD(' '),13,11:
    | ORD('0')..ORD('9'): LinkedListAddAtom(result, MakeIntegerAtom(ParseInteger(l)))
    ELSE LinkedListAddAtom(result, MakeLinkAtom(ParseWord(l)))
    END;
    Advance(l);
  END;
RETURN result END Parse;


(* -------------------------------- Testing --------------------------------- *)

PROCEDURE Test;
VAR l1, l2, l3, n1: List;  ll1: LinkedList;  na, fa: LinkAtom;
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
  NEW(na); na.link := n1;
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
  NEW(fa);  fa.link := MakeText("not a test.");
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
  NEW(fa);  fa.link := MakeText("a test.");
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

  ll1 := MakeLinkedList(NIL);
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicTest));
  LinkedListAddAtom(ll1, MakeIntegerAtom(1234));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicPrintAtom));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicWL));
  Rewind(ll1); Evaluate(ll1);

  ll1 := MakeLinkedList(NIL);
  LinkedListAddAtom(ll1, MakeIntegerAtom(10));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicIota));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicPrintList));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicWL));
  Rewind(ll1); Evaluate(ll1);

  ll1 := MakeLinkedList(NIL);
  LinkedListAddAtom(ll1, MakeIntegerAtom(10));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicIota));
  LinkedListAddAtom(ll1, MakeIntegerAtom(2));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicMultiply));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicPrintList));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicWL));
  Rewind(ll1); Evaluate(ll1);

  ll1 := MakeLinkedList(NIL);
  LinkedListAddAtom(ll1, MakeIntegerAtom(2));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicIota));
  LinkedListAddAtom(ll1, MakeIntegerAtom(10));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicIota));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicMultiply));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicPrintList));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicWL));
  Rewind(ll1); Evaluate(ll1);

  ll1 := MakeLinkedList(NIL);
  LinkedListAddAtom(ll1, MakeIntegerAtom(10));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicIota));
  l2 := MakeLinkedList(MakeLinkedListNode(MakeIntegerAtom(2)));
  LinkedListAddAtom(l2(LinkedList), MakeIntegerAtom(3));
  LinkedListAddAtom(ll1, MakeLinkAtom(l2));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicMultiply));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicPrintList));
  LinkedListAddAtom(ll1, MakeIntrinsic(IntrinsicWL));
  Rewind(ll1); Evaluate(ll1);

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

  NEW(IotaFunctionHandler);
  IotaFunctionHandler.GetAtom := IotaFunctionAtomGetter;
  IotaFunctionHandler.Rewind  := IotaFunctionRewinder;
  IotaFunctionHandler.Advance := IotaFunctionAdvancer;

  NEW(MultiplyFunctionHandler);
  MultiplyFunctionHandler.GetAtom := MultiplyFunctionAtomGetter;
  MultiplyFunctionHandler.Rewind  := MultiplyFunctionRewinder;
  MultiplyFunctionHandler.Advance := MultiplyFunctionAdvancer;

  NEW(SingletonAtomListHandler);
  SingletonAtomListHandler.GetAtom := SingletonAtomListAtomGetter;
  SingletonAtomListHandler.Rewind  := SingletonAtomListRewinder;
  SingletonAtomListHandler.Advance := SingletonAtomListAdvancer;

  NEW(ListEndAtom);

  NEW(OpenNestingRepresentationAtom);  OpenNestingRepresentationAtom.char  := ORD('[');
  NEW(CloseNestingRepresentationAtom); CloseNestingRepresentationAtom.char := ORD(']');

  EmptyList := MakeLinkedList(NIL);


  Test
END fol.
