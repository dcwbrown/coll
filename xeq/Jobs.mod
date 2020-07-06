MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

(* Vague todos:
   o  Define prefix, postfix and dyadic functions
   o  Parse from definitions
   o  Allow over (reduce) implementation to use dyadic functions
   o  Compile. Maybe an IsSingleton fn?
   o  Named value and function definition and invocation
   o  Nested language (and eventually, formatted output)
   o  Distinguish integers and characters just enough
   o  Support partial dyadic operators - where one arg is preset
   o  Less reduction to integer maybe
*)

CONST
  (* Object kinds *)
  Nobj      = 0;    (* None                                *)

  (* Scalar/linked list types *)
  Integer   = 1;    (* a singleton integer value           *)

  (* Other steppables needing a stepper object *)
  Iota      = 8;    (* a vector of 0 up to a limit         *)
  Repeat    = 9;    (* repeats a source multiple times     *)

  (* Operators not needing a stepper object *)
  Negate    = 10;   (* monadic operators                   *)
  Not       = 11;
  Square    = 12;
  Identity  = 13;
  Add       = 14;   (* dyadic operators                    *)
  Subtract  = 15;
  Multiply  = 16;
  Divide    = 17;
  Modulo    = 18;
  And       = 19;
  Or        = 20;
  Equal     = 21;   (* returns 0s and 1s                   *)
  Factorial = 22;

  (* Reduction operators *)
  Match     = 23;   (* walk match tree                     *)
  Merge     = 24;   (* merge into match tree               *)
  Over      = 25;   (* Applicator                          *)

  Stepper   = 26;   (* Steps through algorithmic sequences *)

  (* Tokens *)
  Open      = 27;   (* Parse of '(' *)
  TreeRoot  = 28;   (* Parse of 't' *)

  ObjLimit  = 29;


  (*  ============ object ============      =========== stepper ============
      Kind       p       q       i          p           q          i
      --------   -----   -----   -----      ---------   --------   ---------
      Integer    /       alt     value      first       curr int   curr val
      Iota       parm    /       max        Iota        Iota       curr val
      Repeat     parm1   parm2   iterno     Repeat      Repeat     curr val
      Negate     parm    /       val
      Not        parm    /       val
      Square     parm    /       val
      Add        parm1   parm2   val
      Subtract   parm1   parm2   val
      Multiply   parm1   parm2   val
      Divide     parm1   parm2   val
      Over       parm    /       val
      Stepper    <See cols to right>
  *)

  (*  Reset   - reloads p.i with first value
      More    - returns whether there are more values available
      Advance - steps p.i to the next  value
  *)

TYPE
  Int   = SYSTEM.INT64;
  Ptr   = POINTER TO Obj;
  Obj   = RECORD  kind, i: Int;  n, p, q: Ptr  END;
  OpDef = RECORD  prefix, dyadic, priority: Int  END;

VAR
  Ops:  ARRAY 128 OF OpDef;
  Tree: Ptr;

(* ------------------------------------------------------------------------ *)

PROCEDURE Fail(s: ARRAY OF CHAR);                   BEGIN w.Fail(s)      END Fail;
PROCEDURE Assert(t: BOOLEAN; s: ARRAY [1] OF CHAR); BEGIN w.Assert(t, s) END Assert;

(* ------------------------------------------------------------------------ *)

PROCEDURE NewObj(kind: Int;  p: Ptr;  i: Int): Ptr;
VAR obj: Ptr;
BEGIN Assert(kind # Nobj, "NewObj passed object kind Nobj.");
  NEW(obj);
  obj.kind := kind;  obj.p := p;  obj.i  := i;
RETURN obj END NewObj;

PROCEDURE BoolVal(b: BOOLEAN): Int;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE^ Reset(VAR p: Ptr);
PROCEDURE^ Advance(p: Ptr);
PROCEDURE^ More(p: Ptr): BOOLEAN;

PROCEDURE ResetOver(VAR p: Ptr);
BEGIN Reset(p.p);
  CASE p.q.kind OF
  |Add:      p.i := p.p.i; WHILE More(p.p) DO Advance(p.p); p.i := p.i  +  p.p.i END
  |Subtract: p.i := p.p.i; WHILE More(p.p) DO Advance(p.p); p.i := p.i  -  p.p.i END
  |Multiply: p.i := p.p.i; WHILE More(p.p) DO Advance(p.p); p.i := p.i  *  p.p.i END
  |Divide:   p.i := p.p.i; WHILE More(p.p) DO Advance(p.p); p.i := p.i DIV p.p.i END
  |And:      WHILE (p.p.i # 0) & More(p.p) DO Advance(p.p) END; p.i := BoolVal(p.p.i # 0)
  |Or:       WHILE (p.p.i = 0) & More(p.p) DO Advance(p.p) END; p.i := BoolVal(p.p.i # 0)
  ELSE       w.Fail("Unsupported over operator.")
  END
END ResetOver;

PROCEDURE PrepareToStep(VAR p: Ptr);
BEGIN
  IF (p.kind <= Repeat) OR (p.n # NIL) THEN
    p := NewObj(Stepper, p, 0); Reset(p)
  END
END PrepareToStep;

PROCEDURE MatchPattern(VAR p, k: Ptr);  (* pattern, key *)
BEGIN
  Reset(p);  IF p.kind # Stepper THEN PrepareToStep(p) END;
  Reset(k);  IF k.kind # Stepper THEN PrepareToStep(k) END;
  LOOP
    WHILE (k.i # p.i) & (p.q.q # NIL) DO
      p.q := p.q.q;  p.i := p.q.i
    END;
    IF More(k) & More(p) & (k.i = p.i) THEN
      Advance(k); Advance(p)
    ELSE
      EXIT
    END
  END
END MatchPattern;

PROCEDURE ResetMatch(VAR p: Ptr);
BEGIN
  MatchPattern(p.p, p.q);  (* p is pattern, q is key. *)
  IF (p.p.i # p.q.i) OR More(p.q) THEN
    p.i := 0                (* No match *)
  ELSIF ~More(p.p) THEN
    p.i := 1                (* Match but nothing follows *)
  ELSE
    p := p.p;  Advance(p)  (* Return remaining pattern *)
  END
END ResetMatch;

PROCEDURE ResetMerge(VAR r: Ptr);
VAR p, k: Ptr;  (* Pattern and Key *)
BEGIN
  MatchPattern(r.p, r.q);
  r.i := BoolVal((r.p.i = r.q.i) & ~More(r.q));  (* Success iff whole key matched. *)
  IF r.i # 0 THEN r.i := 0 ELSE  (* Fail if already present *)
    (* Insert current pos in p as alternate in current pos of q *)
    p := r.p;  k := r.q;
    w.Assert(p.kind = Stepper,   "Merge expects pattern to be stepper.");
    w.Assert(p.q.kind = Integer, "Merge expects pattern to execute integer.");
    w.Assert(p.q.q = NIL,        "Merge expects no remaining alternates at mismatch pattern pos.");
    w.Assert(k.kind = Stepper,   "Merge expects key to be stepper.");
    w.Assert(k.q.kind = Integer, "Merge expects key to execute integer.");
    p.q.q := k.q;
    r.i := 1
  END
END ResetMerge;

PROCEDURE Evaluate(p: Ptr);
BEGIN CASE p.kind OF
|Negate:     p.i := -p.p.i
|Not:        p.i := BoolVal(p.p.i = 0)
|Square:     p.i := p.p.i  *  p.p.i
|Add:        p.i := p.p.i  +  p.q.i
|Subtract:   p.i := p.p.i  -  p.q.i
|Multiply:   p.i := p.p.i  *  p.q.i
|Divide:     p.i := p.p.i DIV p.q.i
|Modulo:     p.i := p.p.i MOD p.q.i
|And:        p.i := BoolVal((p.p.i # 0) &  (p.q.i # 0))
|Or:         p.i := BoolVal((p.p.i # 0) OR (p.q.i # 0))
|Equal:      p.i := BoolVal(p.p.i = p.q.i)
ELSE
END END Evaluate;

PROCEDURE Reset(VAR p: Ptr);
BEGIN IF p # NIL THEN CASE p.kind OF
  |Nobj:    Fail("Cannot reset Nobj.")
  |Integer: IF p.n # NIL THEN PrepareToStep(p) END
  |Iota:    Reset(p.p); p.i := p.p.i; PrepareToStep(p)
  |Repeat:  Reset(p.q); PrepareToStep(p)
  |Stepper: p.q := p.p;
            CASE p.q.kind OF
            |Integer: p.i := p.q.i
            |Iota:    p.i := 0
            |Repeat:  Reset(p.q.p); p.q.i := 0; p.i := p.q.p.i
            ELSE      Fail("Stepper references unsteppable in Reset.")
            END
  |Match:   ResetMatch(p)
  |Merge:   ResetMerge(p)
  |Over:    ResetOver(p)
  ELSE      Reset(p.p); Reset(p.q); Evaluate(p)
  END
END END Reset;

PROCEDURE More(p: Ptr): BOOLEAN;
BEGIN
  IF p = NIL THEN RETURN FALSE END;
  CASE p.kind OF
  |Integer, Repeat, Iota, Match, Merge, Over:
            RETURN FALSE  (* If there is more then p will be s stepper *)
  |Stepper: (* w.lc; w.s("More on stepper - "); wref(p); w.s(" -> "); wref(p.p); *)
            IF p.q.n # NIL THEN RETURN TRUE END;
            CASE p.q.kind OF
            |Iota:    RETURN p.i < p.q.i-1
            |Repeat:  RETURN (p.q.i < p.q.q.i-1) OR More(p.q.p)
            ELSE      RETURN FALSE
            END
  ELSE      RETURN More(p.p) OR More(p.q)
  END;
RETURN FALSE END More;

PROCEDURE Advance(p: Ptr);
BEGIN IF p # NIL THEN
  CASE p.kind OF
  |Integer, Repeat, Iota, Match, Merge, Over:  (* No action *)
  |Stepper: Assert(More(p), "No more steppable.");
            CASE p.q.kind OF
            |Integer: p.q := p.q.n;  p.i := p.q.i
            |Iota:    INC(p.i)
            |Repeat:  IF More(p.q.p) THEN Advance(p.q.p);
                      ELSE Reset(p.q.p); INC(p.q.i) END;
                      p.i := p.q.p.i
            ELSE      Fail("Stepper references unsteppable in Advance.")
            END
  ELSE      Advance(p.p); Advance(p.q); Evaluate(p)
  END
END END Advance;

(* ------------------------------------------------------------------------ *)

PROCEDURE wkind(k: Int);
BEGIN CASE k OF
|Nobj:      w.s("Nobj")
|Integer:   w.s("Integer")
|Iota:      w.s("Iota")
|Repeat:    w.s("Repeat")
|Negate:    w.s("Negate")
|Not:       w.s("Not")
|Square:    w.s("Square")
|Identity:  w.s("Identity")
|Add:       w.s("Add")
|Subtract:  w.s("Subtract")
|Multiply:  w.s("Multiply")
|Divide:    w.s("Divide")
|Modulo:    w.s("Modulo")
|And:       w.s("And")
|Or:        w.s("Or")
|Equal:     w.s("Equal")
|Factorial: w.s("Factorial")
|Match:     w.s("Match")
|Merge:     w.s("Merge")
|Over:      w.s("Over")
|Stepper:   w.s("Stepper")
|Open:      w.s("Open")
|TreeRoot:  w.s("TreeRoot")
|ObjLimit:  w.s("ObjLimit")
ELSE       w.s("Unknown-kind")
END END wkind;

(* ------------------------------------------------------------------------ *)

PROCEDURE ImportUTF8(s: ARRAY [1] OF CHAR): Ptr;
VAR i: Int;  first, last: Ptr;

  PROCEDURE ParseUTF8(): Int;
  VAR c, l, n: Int;
  BEGIN
    c := ORD(s[i]);  INC(i);
    IF (i < LEN(s)) & (c >= 128) THEN (* Multi-byte UTF-8 encoding *)
      n := c DIV 16 MOD 4;  (* 0,1: 1 byte follows; 2: 2 bytes; 3 3 bytes. *)
      IF n < 2 THEN c := c MOD 32; l := i+1 ELSE c := c MOD 16; l := i+n END;
      (* c is most sig bits, l is limit of following bytes. *)
      IF l > LEN(s) THEN c := 0FFFDH; i := LEN(s)
      ELSE
        WHILE (i < l) & (ORD(s[i]) DIV 64 = 2) DO
          c := c*64 + ORD(s[i]) MOD 64;  INC(i)
        END;
        IF i # l THEN c := 0FFFDH
        ELSE
          CASE n OF
          |3:  IF (c < 10000H) OR (c > 10FFFFH) THEN c := 0FFFDH END
          |2:  IF (c < 800H) OR (c >= 0D800H) & (c <= 0DFFFH) THEN c := 0FFFDH END
          ELSE IF c < 80H THEN c := 0FFFDH END
          END
        END
      END
    END;
  RETURN c END ParseUTF8;

BEGIN i := 0;
  IF (LEN(s) = 0) OR (s[0] = 0X) THEN RETURN NIL END;
  first := NewObj(Integer, NIL, ParseUTF8());
  last := first;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO
    last.n := NewObj(Integer, NIL, ParseUTF8());
    last := last.n
  END;
RETURN first END ImportUTF8;


PROCEDURE Parse(s: ARRAY [1] OF CHAR): Ptr;
VAR
  characters, tokenFirst, tokenLast, tree: Ptr;
  spaceBefore, tokenPrefix, tokenSuffix: BOOLEAN;

  PROCEDURE IntegerToken;
  VAR acc: Int;
  BEGIN acc := characters.i - 30H;
    WHILE (characters.n   #  NIL)
        & (characters.n.i >= 30H)
        & (characters.n.i <= 39H) DO
      characters := characters.n;
      acc := acc*10 + characters.i - 30H
    END;
    tokenFirst   := characters;
    tokenLast    := characters;
    tokenFirst.i := acc;
    characters   := characters.n;
    tokenFirst.n := NIL
  END IntegerToken;

  PROCEDURE StringToken;
  VAR  delim: Int;  last: Ptr;
  BEGIN
    delim := characters.i;
    tokenFirst := characters.n;
    IF tokenFirst = NIL THEN Fail("Malformed string: nothing after leading delimiter.") END;
    last := tokenFirst;
    WHILE (last.n # NIL) & (last.n.i # delim) DO last := last.n END;
    IF last.n = NIL THEN Fail("Malformed string: no trailing delimiter.") END;
    characters := last.n.n;
    last.n := NIL;
    tokenLast := last
  END StringToken;

  PROCEDURE OperatorToken;
  VAR op: Int;
  BEGIN
    CASE characters.i OF
    |28H:  (* ( *) op := Open
    |7EH:  (* ~ *) op := Not
    |0ACH: (* ¬ *) op := Not
    |69H:  (* i *) op := Iota
    |3DH:  (* = *) op := Equal
    |3FH:  (* ? *) op := Match
    |21H:  (* ! *) op := Merge
    |2BH:  (* + *) op := Add;
    |2DH:  (* - *) op := Subtract
    |2AH:  (* * *) op := Multiply
    |2FH:  (* / *) op := Divide
    |25H:  (* % *) op := Modulo
    |26H:  (* & *) op := And
    |7CH:  (* | *) op := Or
    |72H:  (* r *) op := Repeat
    |74H:  (* t *) op := TreeRoot
    ELSE Fail("Unexpected character in NextToken.")
    END;
    (* Distinguish prefix/infix minus and plus *)
    IF (op = Add) OR (op = Subtract) OR (op = Divide) THEN
      IF spaceBefore & (characters.n # NIL) & (characters.n.i > 20H) THEN
        tokenPrefix := TRUE;
        CASE op OF
        |Add:      op := Identity
        |Subtract: op := Negate
        |Divide:   op := Over
        ELSE
        END
      END
    END;
    IF (op = Merge) & ~spaceBefore THEN
      op := Factorial;
      tokenSuffix := TRUE
    END;
    tokenFirst := characters;
    tokenLast  := characters;
    characters := characters.n;
    tokenFirst.n := NIL;
    tokenFirst.kind := op
  END OperatorToken;

  PROCEDURE ParseToken;
  BEGIN
    tokenFirst  := NIL;   tokenLast   := NIL;
    tokenPrefix := FALSE; tokenSuffix := FALSE;
    WHILE (characters # NIL) & (characters.i <= 20H) DO
      spaceBefore := TRUE;
      characters := characters.n
    END;
    IF characters # NIL THEN
      CASE characters.i OF
      |30H..39H:  IntegerToken   (* 0..9 *)
      |22H,27H:   StringToken    (* ' " *)
      ELSE        OperatorToken
      END
    END;
    spaceBefore := FALSE;
    IF tokenFirst = NIL THEN
      w.sl("        ParseToken complete, no more tokens.")
    ELSE
      w.s("        ParseToken complete: kind "); wkind(tokenFirst.kind);
      w.s(", i "); w.i(tokenFirst.i);
      w.s(", prefix "); w.b(tokenPrefix);
      w.s(", suffix "); w.b(tokenSuffix);
      w.sl(".")
    END
  END ParseToken;

  PROCEDURE ParseScalar(VAR first, last: Ptr);
  VAR dummy: Ptr;
  BEGIN
    w.sl("    ParseScalar.");
    first := tokenFirst;  last := tokenLast;
    IF tokenPrefix THEN
      w.sl("      prefix.");
      ParseToken; ParseScalar(first.p, dummy);  last := first
    ELSIF tokenFirst.kind = Integer THEN
      ParseToken
    ELSE
      Fail("Expected scalar")
    END;
    w.sl("    ParseScalar complete.");
  END ParseScalar;

  PROCEDURE ParseOperand(): Ptr;
  VAR opfirst, oplast, opcopy: Ptr;  prefix: BOOLEAN;
  BEGIN
    w.sl("  ParseOperand.");
    ParseScalar(opfirst, oplast);
    WHILE (tokenFirst # NIL) & (tokenPrefix OR (tokenFirst.kind = Integer)) DO
      w.s(" additional scalar, adding to oplast kind "); wkind(oplast.kind); w.l;
      ParseScalar(oplast.n, oplast)
    END;
    w.sl("  ParseOperand complete.");
  RETURN opfirst END ParseOperand;

  PROCEDURE ParseExpression(level, close: Int): Ptr;  (* close - terminating character *)
  VAR operand, expression: Ptr;
  BEGIN expression := NIL;
    w.sl("ParseExpression.");
    operand := ParseOperand();
    expression := operand;
    w.sl("ParseExpression complete.");
  RETURN expression END ParseExpression;

BEGIN tree := NIL;  spaceBefore := TRUE;  (* Start of text counts as space for prefix detection *)
  w.sl("Parse.");
  characters := ImportUTF8(s);
  w.s("Characters imported, first character "); w.i(characters.i); w.sl(".");
  IF characters # NIL THEN
    ParseToken;
    tree := ParseExpression(0, 0)
  END;
RETURN tree END Parse;


(* ------------------------------------------------------------------------ *)

PROCEDURE Print(p: Ptr);
BEGIN
  Reset(p);  w.i(p.i);  WHILE More(p) DO Advance(p); w.i(p.i) END
END Print;

PROCEDURE PrintTree(p: Ptr; indent: Int);
BEGIN
  wkind(p.kind); w.s(": "); w.i(p.i); w.l;
  IF p.p # NIL THEN w.space(indent); w.s("p: "); PrintTree(p.p, indent+4) END;
  IF p.q # NIL THEN w.space(indent); w.s("q: "); PrintTree(p.q, indent+4) END;
  IF p.n # NIL THEN w.space(indent); w.s("n: "); PrintTree(p.n, indent+4) END;
END PrintTree;

PROCEDURE ColCount(s: ARRAY [1] OF CHAR): Int;
VAR i, c: Int;
BEGIN i := 0;  c := 0;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO
    INC(i);  INC(c);
    IF ORD(s[i-1]) DIV 64 = 3 THEN (* First byte of UTF-8 sequence *)
      WHILE (i < LEN(s)) & (ORD(s[i]) >= 128) & (ORD(s[i]) < 192) DO INC(i) END
    END;
  END;
RETURN c END ColCount;

PROCEDURE^ PriorityParse(s: ARRAY OF CHAR): Ptr;

PROCEDURE TestPriorityParse(ind: Int; s: ARRAY OF CHAR);
VAR i: Int;
BEGIN
  w.s("Pri  "); w.s(s); w.nb; w.s("  ");
  i := ColCount(s);  WHILE i < ind DO w.c(' '); INC(i) END;
  Print(PriorityParse(s)); w.l;
END TestPriorityParse;

PROCEDURE TestParse(ind: Int; s: ARRAY OF CHAR);
VAR  i: Int;  p: Ptr;
BEGIN
  w.l; w.s('Parse "'); w.s(s); w.sl('".');
  p := Parse(s);
  PrintTree(p, 0);
  (* w.s(s);  i := ColCount(s);  WHILE i < ind DO w.c(' '); INC(i) END; *)
  w.s('"'); w.s(s); w.s('" -> '); Print(p); w.l
END TestParse;

PROCEDURE TestParserTwo;
BEGIN
  TestParse(20, "1");
  TestParse(20, "11");
  TestParse(20, "1 1");
  TestParse(20, "-1");
  TestParse(20, "-1 1");
  TestParse(20, "1 -1");
  TestParse(20, "1 -1 1");
END TestParserTwo;

(* ------------------------------------------------------------------------ *)

PROCEDURE PriorityParse(s: ARRAY OF CHAR): Ptr;

CONST  Prefix = 0;     Infix = 1;       Postfix = 2;
       LeftAssoc = 0;  RightAssoc = 1;
VAR
  i: Int;  spacebefore: BOOLEAN;  Ch, Op, Fix, Assoc, Priority: Int;  P : Ptr;


  PROCEDURE ParseUTF8(): Int;
  VAR c, l, n: Int;
  BEGIN
    c := ORD(s[i]);  INC(i);
    IF (i < LEN(s)) & (c >= 128) THEN (* Multi-byte UTF-8 encoding *)
      n := c DIV 16 MOD 4;  (* 0,1: 1 byte follows; 2: 2 bytes; 3 3 bytes. *)
      IF n < 2 THEN c := c MOD 32; l := i+1 ELSE c := c MOD 16; l := i+n END;
      (* c is most sig bits, l is limit of following bytes. *)
      IF l > LEN(s) THEN c := 0FFFDH; i := LEN(s)
      ELSE
        WHILE (i < l) & (ORD(s[i]) DIV 64 = 2) DO
          c := c*64 + ORD(s[i]) MOD 64;  INC(i)
        END;
        IF i # l THEN c := 0FFFDH
        ELSE
          CASE n OF
          |3:  IF (c < 10000H) OR (c > 10FFFFH) THEN c := 0FFFDH END
          |2:  IF (c < 800H) OR (c >= 0D800H) & (c <= 0DFFFH) THEN c := 0FFFDH END
          ELSE IF c < 80H THEN c := 0FFFDH END
          END
        END
      END
    END;
  RETURN c END ParseUTF8;

  PROCEDURE ParseChar(delim: Int): Int;  (* returns 0 at end *)
  VAR c: Int;
  BEGIN
    IF i >= LEN(s) THEN RETURN 0 END;
    IF ORD(s[i]) = delim THEN
      INC(i);
      IF (i < LEN(s)) & (ORD(s[i]) = delim) THEN
        INC(i);  c := delim
      ELSE
        c := 0
      END
    ELSE
      c := ParseUTF8()
    END;
  RETURN c END ParseChar;

  PROCEDURE ParseString(delim: Int): Ptr;
  VAR  result, current: Ptr;  c: Int;
  BEGIN
    c := ParseChar(delim);
    result := NewObj(Integer, NIL, c);
    IF c # 0 THEN
      current := result;
      c := ParseChar(delim);
      WHILE c # 0 DO
        current.n := NewObj(Integer, NIL, c);
        current := current.n;
        c := ParseChar(delim);
      END
    END;
  RETURN result END ParseString;


  PROCEDURE skipSpace;
  BEGIN WHILE (i < LEN(s))  &  (s[i] > 0X)  &  (s[i] <= ' ') DO INC(i) END
  END skipSpace;

  PROCEDURE expect(c: CHAR);
  BEGIN skipSpace;
    Assert(s[i] = c, "Unexpected character in PriorityParse");
    INC(i)
  END expect;

  PROCEDURE ParseInt(VAR s: ARRAY OF CHAR; VAR i: Int): Int;
  VAR acc: Int;
  BEGIN acc := 0;
    WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
      acc := acc*10 + ORD(s[i]) - ORD('0');  INC(i)
    END;
  RETURN acc END ParseInt;

  PROCEDURE ParseIntegers(): Ptr;
  VAR result, current: Ptr;
  BEGIN
    result := NewObj(Integer, NIL, ParseInt(s, i));  skipSpace;
    IF (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') THEN
      current := result;
      WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
        current.n := NewObj(Integer, NIL, ParseInt(s, i));
        current := current.n;  skipSpace
      END
    END;
  RETURN result END ParseIntegers;

  PROCEDURE^ ParseDyadic(priority: Int): Ptr;

  PROCEDURE ParseOperation(VAR op: OpDef);
  BEGIN  skipSpace;  op := Ops[ORD(s[i])]  END ParseOperation;

  PROCEDURE ParseOperand(): Ptr;
  VAR  result, link: Ptr;  op: OpDef;  val: Int;
  BEGIN skipSpace;
    CASE s[i] OF
    |'(':      INC(i);  result := ParseDyadic(0);  skipSpace;  expect(')')
    |'/':      INC(i);  ParseOperation(op);
               Assert(op.dyadic # Nobj, "Expected dyadic operator following '/'.");
               INC(i);
               result := NewObj(Over, ParseOperand(), 0);
               result.q := NewObj(op.dyadic, NIL, 0)
    |'0'..'9': result := ParseIntegers()
    |'"':      INC(i);  result := ParseString(ORD('"'))
    |"'":      INC(i);  result := ParseString(ORD("'"))
    |'t':      INC(i);  result := Tree;
    ELSE       ParseOperation(op);  INC(i);
               IF op.prefix = Identity THEN result := ParseOperand()
               ELSE result := NewObj(op.prefix, ParseOperand(), 0) END
    END;
  RETURN result END ParseOperand;


  PROCEDURE ParseDyadic(priority: Int): Ptr;
  VAR  p: Ptr;  op: OpDef;
  BEGIN  p := ParseOperand();
    ParseOperation(op);
    WHILE op.priority >= priority DO
      INC(i);
      p    := NewObj(op.dyadic, p, 0);
      p.q :=  ParseDyadic(op.priority+1);
      ParseOperation(op)
    END;
  RETURN p END ParseDyadic;

BEGIN i := 0;
  RETURN ParseDyadic(0)
END PriorityParse;


(*--------------------------------------------------------------------------*)

PROCEDURE TestParserOne;
BEGIN
  Tree := NewObj(Integer, NIL, ORD('/'));

  TestPriorityParse(50, "/&( 1                 = 1 )");
  TestPriorityParse(50, "/&( 1+2-(5-1)         = -1 )");
  TestPriorityParse(50, "/&( 1-2-3-4           = -8 )");
  TestPriorityParse(50, "/&( 2*3+1             = 7 )");
  TestPriorityParse(50, "/&( 1+2*3             = 7 )");
  TestPriorityParse(50, "/&( 1+2*3+4           = 11 )");
  TestPriorityParse(50, "/&( 1 2 3 4           = 1 2 3 4 )");
  TestPriorityParse(50, "/&( 1 2 + 3 4         = 4 6 )");
  TestPriorityParse(50, "/&( 1 2 3 4 + 10      = 11 12 13 14 )");
  TestPriorityParse(50, "/&( i4                = 0 1 2 3 )");
  TestPriorityParse(50, "/&( i4+1              = 1 2 3 4 )");
  TestPriorityParse(50, "/&( 1+2*i4            = 1 3 5 7 )");
  TestPriorityParse(50, "/&( 1+i4*2            = 1 3 5 7 )");
  TestPriorityParse(50, "/&( 1 2 3 4 r 3       = 1 2 3 4 1 2 3 4 1 2 3 4 )");
  TestPriorityParse(50, "/&( i4r3              = 0 1 2 3 0 1 2 3 0 1 2 3 )");
  TestPriorityParse(50, "/&( /+5               = 5 )");
  TestPriorityParse(50, "/&( /+i5              = 10 )");
  TestPriorityParse(50, "/&( /-i5              = -10 )");
  TestPriorityParse(50, "/&( /*i5              = 0 )");
  TestPriorityParse(50, "/&( /*(i5+1)          = 120 )");
  TestPriorityParse(50, "/&( /+ 5 15 27        = 47 )");
  TestPriorityParse(50, "/&( ''                = 0 )");
  TestPriorityParse(50, "/&( 'A'               = 65 )");
  TestPriorityParse(50, "/&( '123'             = 49 50 51 )");
  TestPriorityParse(50, '/&( "123"             = 49 50 51 )');
  TestPriorityParse(50, '/&( "!""#"            = 33 34 35 )');
  TestPriorityParse(50, '/&( "¬¦é€£"           = 172 166 233 8364 163 )');
  TestPriorityParse(50, "/&( 1 2 3 4 = 1 3 2 4 = 1 0 0 1 )");
  TestPriorityParse(50, "/&( 'abcde' = 'axcxe' = 1 0 1 0 1 )");
  TestPriorityParse(50, "/&( 1 2 3 ? 1 2 3     = 1 )");
  TestPriorityParse(50, "/&( 1 2 3 4 ? 1 9 9 4 = 0 )");
  TestPriorityParse(50, "/&( i4 ? 0 1 2 3      = 1 )");
  TestPriorityParse(50, "/&( 0 1 2 3 ? i4      = 1 )");
  TestPriorityParse(50, "/&( 'abc' ! 'alpha'   = 1 )");
  TestPriorityParse(50, "/&( 'abc' ! 'beta'    = 1 )");
  TestPriorityParse(50, "/&( 'abc' ! 'abc'     = 0 )");
  TestPriorityParse(50, "/&( t                 = 47 )");
  TestPriorityParse(50, "/&( t ! 'alpha'       = 1 )");
  TestPriorityParse(50, "/&( t ! 'beta'        = 1 )");
  TestPriorityParse(50, "/&( t ! 'abc'         = 1 )");
  TestPriorityParse(50, "/&( t ! 'abc'         = 0 )");
  TestPriorityParse(50, "/&( t ? 'abc'         = 1 )");
  TestPriorityParse(50, "/&( t ? 'al'          = 112 104 97 )");
  TestPriorityParse(50, "/&( t ? 'be'          = 116 97 )");
END TestParserOne;


PROCEDURE Test*;
BEGIN
  TestParserOne;
  TestParserTwo
END Test;

(* ------------------------------------------------------------------------ *)

PROCEDURE DefOp(c: CHAR; prefix, dyadic, priority: Int);
BEGIN
  Ops[ORD(c)].prefix   := prefix;
  Ops[ORD(c)].dyadic   := dyadic;
  Ops[ORD(c)].priority := priority
END DefOp;

PROCEDURE InitOpLevel;
VAR i: Int;
BEGIN
  FOR i := 0 TO 127 DO
    Ops[i].prefix   := Nobj;
    Ops[i].dyadic   := Nobj;
    Ops[i].priority := -1
  END;

  (*         Prefix    Dyadic   Priority *)
  DefOp('~', Not,      Nobj,    -1);
  DefOp('i', Iota,     Nobj,    -1);
  DefOp('=', Nobj,     Equal,    0);
  DefOp('?', Nobj,     Match,    0);
  DefOp('!', Nobj,     Merge,    1);
  DefOp('+', Identity, Add,      1);
  DefOp('-', Negate,   Subtract, 1);
  DefOp('*', Nobj,     Multiply, 2);
  DefOp('/', Nobj,     Divide,   2);
  DefOp('%', Nobj,     Modulo,   2);
  DefOp('&', Nobj,     And,      2);
  DefOp('|', Nobj,     Or,       2);
  DefOp('r', Nobj,     Repeat,   3)
END InitOpLevel;

BEGIN  InitOpLevel;  Tree := NewObj(Integer, NIL, ORD('/'))
END Jobs.


------------------------------------------------------------------------------


PROCEDURE wtree(p: Ptr; nest: Int);
BEGIN
  IF p = NIL THEN w.sl("NIL.") END;
  wkind(p.kind); w.s(" i="); w.nb; w.i(p.i); w.l;
  IF p.p # NIL THEN
    w.lc; w.space(nest*4); w.s("p: "); wtree(p.p, nest+1)
  END;
  IF p.q # NIL THEN
    w.lc; w.space(nest*4); w.s("q: "); wtree(p.q, nest+1)
  END;
END wtree;
