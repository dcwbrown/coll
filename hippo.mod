MODULE hippo;  (* hippo - a loose reference to the hippocampus *)

IMPORT Strings, TextWriter, SYSTEM;

CONST
  NumIntrinsics = 128;

  (* Actions *)
  PushFirst = 0;
  PushNext  = 1;

TYPE
  i8  = SYSTEM.INT8;
  i64 = SYSTEM.INT64;

  Source = POINTER TO SourceRec;
  Atom   = POINTER TO AtomRec;   AtomRec = RECORD END;

  Advancer = PROCEDURE(s: Source);

  SourceRec = RECORD
    current: Atom;
    advance: Advancer;
  END;

  Val = POINTER TO ValRec;  ValRec = RECORD (AtomRec) v: i64    END;
  Ref = POINTER TO RefRec;  RefRec = RECORD (AtomRec) s: Source END;

  List = POINTER TO ListRec; ListRec = RECORD atom: Atom; prev, next: List END;

  ListSource = POINTER TO ListSourceRec; ListSourceRec = RECORD (SourceRec)
    node: List;
  END;

  NumberSource = POINTER TO NumberSourceRec; NumberSourceRec = RECORD (SourceRec)
    param:  Source;
    string: ARRAY 30 OF CHAR;
    offset: INTEGER;
  END;

VAR
  Abort: BOOLEAN;


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
BEGIN IF Strings.Length(msg) > 0 THEN wlc; ws("Internal error:"); wsl(msg)END;
  wlc; HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* --------------------------------- Lists ---------------------------------- *)

PROCEDURE AdvanceList(s: Source);
BEGIN
  s.current := NIL;
  WITH s: ListSource DO
    IF s.node # NIL THEN
      s.node := s.node.next;
      IF s.node # NIL THEN s.current := s.node.atom END
    END
  END
END AdvanceList;


(* ---------------------------- Number formatter ---------------------------- *)

PROCEDURE FormatNumber(i: i64; VAR s: ARRAY OF CHAR; VAR o: INTEGER);
BEGIN
  IF i<0 THEN
    s[o] := '-'; INC(o); FormatNumber(-i, s, o)
  ELSE
    IF i > 9 THEN FormatNumber(i DIV 10, s, o) END;
    s[o] := CHR(ORD('0') + i MOD 10);
    INC(o);
    s[o] := 0X;
  END
END FormatNumber;

PROCEDURE AdvanceNumber(s: Source);
VAR ns: NumberSource; o: INTEGER;
BEGIN
  IF s.current # NIL THEN
    WITH s: NumberSource DO ns := s END;
    Assert(s # NIL, "s non-null");
    IF ns.string[ns.offset] # 0X THEN
      (* The next character is already formatted *)
      ns.current(Val).v := ORD(ns.string[ns.offset]);
      INC(ns.offset)
    ELSE
      (* Reached end of one number. Look for and format the next. *)
      ns.param.advance(ns.param);
      IF ns.param.current = NIL THEN
        ns.current := NIL
      ELSE
        ns.offset := 0;
        FormatNumber(ns.param.current(Val).v, ns.string, ns.offset);
        ns.offset := 0;
        ns.current(Val).v := ORD(' ')
      END
    END
  END
END AdvanceNumber;

PROCEDURE MakeNumberer(s: Source): Source;
VAR result: NumberSource;  v: Val;
BEGIN
  NEW(result);  result.advance := AdvanceNumber;
  result.param := s;  result.offset := -1;
  IF s.current = NIL THEN
    result.current := NIL
  ELSE
    Assert(s.current IS Val, "Expected Val in MakeNumberer");
    NEW(v); result.current := v;
    result.offset := 0;
    FormatNumber(s.current(Val).v, result.string, result.offset);
    result.current(Val).v := ORD(result.string[0]);
    result.offset := 1;
  END;
RETURN result END MakeNumberer;


(* ------------------------------- Write items ------------------------------ *)

PROCEDURE WriteSource(s: Source);
VAR c: CHAR;
BEGIN
  WHILE s.current # NIL DO
    IF s.current IS Val THEN
      c := CHR(s.current(Val).v);
      IF (c = '^') OR (c = '[') OR (c = ']') THEN wc('^') END;
      wc(c)
    ELSE
      wc('['); WriteSource(s.current(Ref).s); wc(']')
    END;
    s.advance(s);
  END;
END WriteSource;


(* -------------------------------- Testing --------------------------------- *)

PROCEDURE MakeString(str: ARRAY OF CHAR): ListSource;
VAR s: ListSource; l: List; v: Val; i: INTEGER;
BEGIN
  NEW(s);  s.advance := AdvanceList;
  IF (LEN(str) > 0) & (str[0] # 0X) THEN
    NEW(l);  s.node := l;
    NEW(v);  v.v := ORD(str[0]);  l.atom := v;
    i := 1;
    WHILE (i < LEN(str)) & (str[i] # 0X) DO
      NEW(l.next);  l.next.prev := l;  l := l.next;
      NEW(v);  v.v := ORD(str[i]);  l.atom := v;
      INC(i)
    END;
    s.current := s.node.atom
  END;
RETURN s END MakeString;

PROCEDURE Test;
  VAR s: Source;
BEGIN
  s := MakeString("Hello");
  WriteSource(s); wl;

  s := MakeNumberer(MakeString("abcde"));
  WriteSource(s); wl;
  wlc
END Test;

BEGIN Abort := FALSE;
  Test
END hippo.


  DequeValRec  = RECORD (ValRec) prev, next: Atom END;
  DequeRefRec  = RECORD (RefRec) prev, next: Atom END;
  DequeSource  = RECORD (SourceRec) curr: Atom END;

VAR
   Abort:  BOOLEAN;
   Rack:   ARRAY 100 OF Source;
   Free:   i8;  (* Next free slot on the rack *)
   Mark:   i8;  (* Current base of operations on the rack *)
   Store:  Ref;
   Input:  Source;


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
BEGIN IF Strings.Length(msg) > 0 THEN wlc; ws("Internal error:"); wsl(msg)END;
  wlc; HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* ------------------------------- Dump items ------------------------------- *)

PROCEDURE DumpInt(i: i64);
BEGIN
  wi(i);
  IF (i >= 32) & (i < 127) THEN ws("-'"); wc(CHR(i)); wc("'") END;
  (*IF Intrinsics[i] # NIL THEN ws("-<"); ws(IntrinsicNames[i]); ws(">") END;*)
  wc(' ')
END DumpInt;

(*
PROCEDURE DumpItem(i: Item);
BEGIN
  IF i IS Ref THEN wc('['); DumpItem(i(Ref).r); wc(']') ELSE DumpInt(i(Val).i) END;
END DumpItem;

PROCEDURE DumpList(i: Item);
BEGIN WHILE i # NIL DO DumpItem(i);  i := i.next END
END DumpList;
*)

(* --------------------------- Item construction ---------------------------- *)

PROCEDURE MakeVal(v: i64): Val;  VAR n: Val;
BEGIN NEW(n); n.v := v; RETURN n END MakeVal;

PROCEDURE MakeRef(i: Item): Ref;  VAR n: Ref;
BEGIN NEW(n); n.r := i; RETURN n END MakeRef;

PROCEDURE MakeCopy(i: Item): Item;
BEGIN IF i IS Val THEN RETURN MakeVal(i(Val).v) ELSE RETURN MakeRef(i(Ref).r) END
END MakeCopy;


(* ------------------------------- Sources ---------------------------------- *)

PROCEDURE LookupContext(i: Item): Context;
BEGIN Assert((i IS Val)
          &  (i.v >= 0)
          &  (i.v < NumIntrinsics)
          &  (Intrinsics[i.v] # NIL),
          "Not a context index.");
RETURN Intrinsics[i.v] END LookupContext;

PROCEDURE SourceNext(VAR s: Source): i64;
VAR result: i64; n: Source;
BEGIN
  IF s.top IS Val THEN
    result := s.top.v;
    IF s.top.next # NIL THEN s.top := s.top.next ELSE s.top := s.prev END
  ELSE
    (* s.top is a reference to the first entry in a nested list. This entry is
       always the index of a procedure that can create a new source level and
       return its values one by one. *)
    NEW(n);  NEW(n.top);
    n.top.c := LookupContext(s.top);
    n.top.i := s.next;
    n.prev  := s;
    s := n
  END
END SourceNext;


(* ------------------------------- Contexts --------------------------------- *)

PROCEDURE LookupIntrinsic(i: i64): Action;
BEGIN Assert((i >= 0)
          &  (i < NumIntrinsics)
          &  (Intrinsics[i] # NIL),
          "Not an intrinsic.");
RETURN Intrinsics[i] END LookupIntrinsic;

PROCEDURE ^ProcessRef(i: Item);

PROCEDURE ProcessItem(i: Item);
BEGIN IF i IS Val THEN Context(i) ELSE ProcessRef(i(Ref).r) END
END ProcessItem;

PROCEDURE ProcessRef(i: Item);  (* Item is first of list *)
VAR oldContext: Action;
BEGIN
  oldContext := Context;  Context := LookupIntrinsic(i(Val).i);  i := i.next;
  WHILE i # NIL DO  ProcessItem(i);  i := i.next  END;
  Context := oldContext
END ProcessRef;

PROCEDURE PrintChar(i: Item);
VAR n: i64;
BEGIN n := i(Val).i;
  IF     n = 10                THEN wl
  ELSIF (n >= 32) & (n <= 126) THEN wc(CHR(n))
  ELSE                              wc("?") END
END PrintChar;

PROCEDURE PrintInt(i: Item);
BEGIN wi(i(Val).i)
END PrintInt;

PROCEDURE Evaluate(VAR i: Item);
VAR action: Action;
BEGIN
  action := LookupIntrinsic(i(Val).i);
  action(i)
END Evaluate;


(* ------------------------------ Experiments ------------------------------- *)

PROCEDURE MakeCharList(s: ARRAY OF CHAR): Item;
VAR o: INTEGER; first, i: Item;
BEGIN
  o := 0;
  first := MakeVal(1); i := first;
  WHILE (o < LEN(s)) & (s[o] # 0X) DO
    i.next := MakeVal(ORD(s[o]));  i.next.prev := i;
    INC(o);  i := i.next
  END;
RETURN first END MakeCharList;

PROCEDURE Test;
BEGIN
  Intrinsics[1] := PrintChar;  IntrinsicNames[1] := "PrintChar";
  Intrinsics[2] := PrintInt;   IntrinsicNames[2] := "PrintInt";
  Input.r := MakeCharList("Hello");
  (*DumpList(Input.r)*)
  ProcessRef(Input.r); wl;
  Input.r(Val).i := 2;
  ProcessRef(Input.r); wl;
END Test;


(* -------------------------------- Startup --------------------------------- *)

BEGIN
  Abort:=FALSE; Free:=0; Mark:=0; Context:=PrintChar;
  IF SIZE(i64) # 8 THEN ws("SIZE(i64) = "); wi(SIZE(i64)); ws(", must be 8."); Fail("") END;
  NEW(Store); NEW(Input); NEW(Output);
  Test;
  wlc
END hippo.


























splurgle crunge splotinabulous

PROCEDURE BreakBefore(n: Item);
BEGIN IF (n # NIL) & (n.prev # NIL) THEN n.prev.next := NIL; n.prev := NIL END
END BreakBefore;

PROCEDURE Join(n1, n2: Item);
(* Ref n1 to n2 via n1.next and n2.prev.
   If n1.next is already not nil, add a link node between n1 and n2
   whose link references the old n1.next. *)
VAR link: Ref;
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

(* ------------------------------ Item stacking ----------------------------- *)

PROCEDURE Push(n: Item);
VAR copy: Item;
BEGIN copy := MakeCopy(n); Join(copy, Rack); Rack := copy;
END Push;

PROCEDURE Dup;   BEGIN Push(Rack) END Dup;
PROCEDURE Drop;  BEGIN Rack := Rack.next; BreakBefore(Rack) END Drop;

PROCEDURE Swap;
VAR n1, n2, n3: Item;
BEGIN
  n2 := Rack;  n1 := n2.next;  n3 := n1.next;
  (* Relink in the order n1 n2 n3 *)
  n1.prev := NIL;  n1.next := n2;
  n2.prev := n1;   n2.next := n3;
  IF n3 # NIL THEN n3.prev := n2 END;
  Rack := n1;
END Swap;


(* ------------------------------- Intrinsics ------------------------------- *)

(*
PROCEDURE Constant(n: Item): Item;
BEGIN n := n.next; Push(n);
RETURN n.next END Constant;
*)

PROCEDURE Print;
BEGIN
  IF    Rack IS Val     THEN wi(Rack(Val).i)
  ELSIF Rack IS InstructionItem THEN PrintInstruction(Rack(InstructionItem).i)
  ELSIF Rack IS Ref        THEN wc('['); DumpList(Rack(Ref).l); wc(']')
  ELSE ws("[#FAULTY#]")
  END;
  Drop;
END Print;

PROCEDURE AddIntToList(i: i64; n: Item);
BEGIN
  WHILE n # NIL DO
    WITH n: Val DO INC(n.i, i)
    ELSE AddIntToList(i, n(Ref).l)
    END;
    n := n.next
  END
END AddIntToList;

PROCEDURE AddListToList(n1, n2: Item);
BEGIN
  WHILE (n1 # NIL) & (n2 # NIL) DO
    IF n1 IS Val THEN
      IF n2 IS Val THEN
        INC(n2(Val).i, n1(Val).i)
      ELSE (* n2 is link node *)
        AddIntToList(n1(Val).i, n2(Ref).l)
      END
    ELSE (* n1 is link node *)
      IF n2 IS Val THEN
        AddIntToList(n2(Val).i, n1(Ref).l)
      ELSE (* n2 is link node *)
        AddListToList(n1(Ref).l, n2(Ref).l)
      END
    END;
    n1 := n1.next;
    n2 := n2.next
  END
END AddListToList;

PROCEDURE Add;
BEGIN
  IF (Rack IS Val) = (Rack.next IS Val) THEN
    IF Rack IS Val THEN
      INC(Rack.next(Val).i, Rack(Val).i)
    ELSE
      AddListToList(Rack(Ref).l, Rack.next(Ref).l)
    END
  ELSE (* One is int, one is list *)
    IF Rack.next IS Val THEN Swap END;
    AddIntToList(Rack(Val).i, Rack.next(Ref).l)
  END;
  Drop
END Add;


PROCEDURE MakeInstruction(i: i64): InstructionItem;
VAR result: InstructionItem;
BEGIN NEW(result); result.i := i; RETURN result END MakeInstruction;

PROCEDURE MakeRef(l: Item): Ref;
VAR result: Ref;
BEGIN NEW(result); result.l := l; RETURN result END MakeRef;

PROCEDURE ^ParseNest;

PROCEDURE Intrinsic(n: InstructionItem): Item;
VAR next: Item;
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
  | DoSymbol:    Push(MakeRef(n))
  ELSE Fail("Execute undefined intrinsic.")
  END;
RETURN next END Intrinsic;

PROCEDURE Execute(n: Item);
BEGIN
  WHILE n # NIL DO
    IF n IS InstructionItem THEN
      n := Intrinsic(n(InstructionItem))
    ELSE
      Push(n); n := n.next
    END
  END
END Execute;


(* --------------------------------- Store ---------------------------------- *)

PROCEDURE MatchInt(n: Item; i: i64): Item;
(* Returns the Val with value i that matches starting
  at n, or NIL if there is no match.
  If n is an Val it's a simple value test.
  If n is a Ref it's a recursive search for a match through
  both the .l and .next links. *)
VAR result: Item;
BEGIN result := NIL;
  IF n # NIL THEN
    IF (n IS Val) & (n(Val).i = i) THEN
      result := n
    ELSIF n IS Ref THEN
      result := MatchInt(n(Ref).l, i);
      IF result = NIL THEN result := MatchInt(n.next, i) END
    END
  END;
RETURN result END MatchInt;

PROCEDURE MatchItem(store, list: Item): Item;
BEGIN
  IF (list = NIL) OR ~(list IS Val) THEN RETURN NIL END;
  RETURN MatchInt(store, list(Val).i)
END MatchItem;

PROCEDURE MatchStore(VAR store, list: Item);
(* Advances store and list forward while store.next matches list *)
(* Entry: store.next is where to start searching the store *)
(* Exit:  store is the node to which the remainder of list should be joined *)
VAR match: Item;
BEGIN
  match := MatchItem(store.next, list);
  WHILE match # NIL DO
    store := match;
    list  := list.next;
    match := MatchItem(store.next, list)
  END
END MatchStore;

PROCEDURE Save(n: Item);
VAR s: Item;
BEGIN
  s := Store;
  MatchStore(s, n);
  Join(s, n)
END Save;


(* -------------------------------- Parsing --------------------------------- *)

PROCEDURE IsWhiteSpace(n: Item): BOOLEAN;
BEGIN RETURN (n IS Val) & (n(Val).i <= 32) END IsWhiteSpace;

PROCEDURE IsAlphanumeric(n: Item): BOOLEAN;
BEGIN
  (* wsl("IsAlphanumericItem."); *)
  WITH n: Val DO RETURN
       (n.i >= ORD('0'))
    & ((n.i <= ORD('9')) OR (n.i >= ORD('A')))
    & ((n.i <= ORD('Z')) OR (n.i >= ORD('a')))
    &  (n.i <= ORD('z'));
  ELSE RETURN FALSE
  END
END IsAlphanumeric;

PROCEDURE IsCharacter(n: Item; c: CHAR): BOOLEAN;
BEGIN WITH n: Val DO RETURN n.i = ORD(c) ELSE RETURN FALSE END
END IsCharacter;

PROCEDURE MatchAnyInstruction(n: Item): Item;
(* Returns an InstructionItem or NIL.
  If n is an InstructioItem, returns that.
  If n is an Val, returns NIL.
  If n is a Ref it's a recursive search for an instruction node through
  both the .l and .next links. *)
VAR result: Item;
BEGIN result := NIL;
  (* wsl("Begin MatchAnyInstruction."); *)
  IF n # NIL THEN
    IF n IS InstructionItem THEN
      result := n
    ELSIF n IS Ref THEN
      result := MatchAnyInstruction(n(Ref).l);
      IF result = NIL THEN result := MatchAnyInstruction(n.next) END
    END
  END;
RETURN result END MatchAnyInstruction;

PROCEDURE ParseNest;
VAR root: Item; depth: INTEGER;
BEGIN
  root := MakeRef(Input.l);
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
VAR s, end: Item;
BEGIN
  WHILE Input.l # NIL DO
    IF Input.l IS Ref THEN
      Push(Input.l); Input.l := Input.l.next
    ELSIF Input.l IS InstructionItem THEN
      Input.l := Intrinsic(Input.l(InstructionItem))
    ELSIF Input.l IS Val THEN
      IF Input.l(Val).i <= 32 THEN
        Input.l := Input.l.next  (* Skip white space *)
      ELSE
        ws("Parsing: "); PrintList(Input.l); wl;
        IF Input.l # NIL THEN
          s := Store;
          end := Input.l;
          MatchStore(s, end);
          (*
          ws("MatchStore complete. s is "); DumpItem(s);
          ws(" ... end is "); DumpItem(end);
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

PROCEDURE MakeInteger(i: i64): Val;
VAR result: Val;
BEGIN NEW(result); result.i := i; RETURN result END MakeInteger;

(*
PROCEDURE SubstringToList(s: ARRAY OF CHAR; VAR i: i64; l: i64): Item;
VAR root, last, addition: Item;
BEGIN
  NEW(root); last := root;
  WHILE (i<l) & (s[i] # ']') DO
    IF s[i] = '[' THEN
      INC(i);
      addition := MakeRef(SubstringToList(s, i, l));
      addition(Ref).l.prev := addition
    ELSE
      addition := MakeInteger(ORD(s[i]));
      INC(i)
    END;
    Join(last, addition);
    last := last.next
  END;
  IF i<l THEN INC(i) END; ( * Step over ']' * )
RETURN root.next END SubstringToList;

PROCEDURE StringToList(s: ARRAY OF CHAR): Item;
VAR i, l: i64;
BEGIN i := 0; l := Strings.Length(s);
RETURN SubstringToList(s, i, l) END StringToList;
*)

PROCEDURE StringToList(s: ARRAY OF CHAR): Item;
VAR root, last: Item; i: i64;
BEGIN
  NEW(root);  last := root;  i := 0;
  WHILE (i<LEN(s)) & (s[i] # 0X) DO
    Join(last, MakeInteger(ORD(s[i])));
    last := last.next;
    INC(i)
  END;
RETURN root.next END StringToList;

PROCEDURE TestAddItem;
VAR n1, n2, n3, n4: Item;
BEGIN
  wsl("MakeInteger n1.");  n1 := MakeInteger(48+1);
  wsl("MakeInteger n3.");  n3 := MakeInteger(48+2);
  wsl("MakeInteger n4.");  n4 := MakeInteger(48+3);
  wsl("MakeRef n2."); n2 := MakeRef(n4);
  Join(n1, n2);
  Join(n2, n3);
  ws("n1:"); DumpItem(n1);
  ws("n2:"); DumpItem(n2);
  ws("n3:"); DumpItem(n3);
  ws("n4:"); DumpItem(n4);
  DumpList(n1); wl;
END TestAddItem;

PROCEDURE VerifyRefs(first: Item);
VAR n: Item;
BEGIN n := first;
  WHILE n # NIL DO
    Assert((n.next = NIL) OR (n.next.prev = n), "n.next.prev = n");
    WITH n: Ref DO
      Assert((n.l = NIL) OR (n.l.prev = n), "n.l.prev = n");
      VerifyRefs(n.l)
    ELSE END;
    n := n.next;
  END
END VerifyRefs;

PROCEDURE TestExecute;
VAR n1, n2, n3, n4: Item;
BEGIN
  n1 := MakeInteger(2);
  n2 := MakeInteger(3);            Join(n1, n2);
  n3 := MakeInstruction(DoAdd);    Join(n2, n3);
  n4 := MakeInstruction(DoPrint);  Join(n3, n4);
  DumpItemList(n1,0); wl;
  VerifyRefs(Rack);
  Execute(n1); wl;
  VerifyRefs(Rack);
END TestExecute;


PROCEDURE PrintStore(n: Item; column: i64);
TYPE
  pending = POINTER TO pendingRec;
  pendingRec = RECORD
    next: pending;
    node: Item;
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
      n: Val DO
        IF (n.i > 31) & (n.i < 127) THEN wc(CHR(n.i)) ELSE wc("?") END;
        INC(column);
    | n: InstructionItem DO PrintInstruction(n.i)
    | n: Ref DO
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
VAR store, key: Item;
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
VAR s,n: Item;
BEGIN
  Save(StringToList("The cat sat on the mat."));
  Save(StringToList("The cow jumped over the moon."));
  Save(StringToList("Another line altogether."));
  Save(StringToList("The quick brown fox jumps over the lazy dog."));
  Save(StringToList("The little dog laughed to see such fun."));
  Save(StringToList("The dish ran away with the spoon."));
  Save(StringToList("A list with a [nested] part."));

  (* DumpItemList(Store, 0); *)
  VerifyRefs(Store);
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
  wsl("Before swap:"); DumpItemList(Rack,2); VerifyRefs(Rack);
  Swap;
  wsl("After swap:");  DumpItemList(Rack,2); VerifyRefs(Rack);
END TestSwap;

PROCEDURE TestParse;
VAR n1, n2, n3, n4, n5: Item;
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
  Rack := NIL;
  wsl("Store before parse:"); PrintStore(Store,0);
  Input.l := StringToList("the cat sat hi on the cat [nested part] the cat");
  Parse;
  ws("Rack: "); PrintList(Rack); wl;
  wsl("Store: "); PrintStore(Store,0);


  (* Test parsing of nests using hippo definition of '[' *)
  NEW(Store); Rack := NIL;

  (* Define '[' *)
  n1 := MakeInteger(ORD('[')); n2 := MakeInstruction(DoParseNest); Join(n1, n2);
  Save(n1);
  Input.l := StringToList("A [nested] test.");
  Parse;
  ws("Rack: "); PrintList(Rack); wl;
  wsl("Store: "); PrintStore(Store,0);

END TestParse;

BEGIN Abort:=FALSE; Rack:=NIL; NEW(Store); NEW(Input); NEW(Output);
  wsl("Folio test.");
  IF SIZE(i64) # 8 THEN
    ws("SIZE(i64) = "); wi(SIZE(i64)); ws(", must be 8."); Fail("")
  END;
  TestAddItem;
  TestExecute;
  TestStore;
  TestSwap;
  TestParse;
END hippo.
