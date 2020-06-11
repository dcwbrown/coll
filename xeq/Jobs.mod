MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

(* Vague todos:
   o  Allow sequences to contain nested evaluations?
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
  Nobj      = 0;                  (* None                                *)

  (* Scalar/linked list types *)
  Integer   = 1;                  (* a singleton integer value           *)

  Reference = 7;                  (* evaluation within literal vector    *)

  (* Other steppables needing a stepper object *)
  Iota      = 8;                  (* a vector of 0 up to a limit         *)
  Repeat    = 9;                  (* repeats a source multiple times     *)

  (* Operators not needing a stepper object *)
  Negate    = 10;  Not      = 11; (* monadic operators                   *)
  Square    = 12;  Identity = 13; (* monadic operators                   *)
  Add       = 14;  Subtract = 15; (* dyadic operators                    *)
  Multiply  = 16;  Divide   = 17; (* dyadic operators                    *)
  And       = 18;  Or       = 19; (* dyadic operators                    *)
  Equal     = 20;                 (* returns 0s and 1s                   *)

  (* Reduction operators *)
  Match     = 21;                 (* walk match tree                     *)
  Merge     = 22;                 (* merge into match tree               *)
  Over      = 23;                 (* Applicator                          *)

  Stepper   = 24;                 (* Steps through algorithmic sequences *)
  ObjLimit  = 25;

  (*  ============ object ============      =========== stepper ============
      Kind       p1      p2      i          p1          p2         i
      --------   -----   -----   -----      ---------   --------   ---------
      Integer    next    alt     value      first int   curr int   curr val
      Iota       parm    /       max        Iota        /          curr val
      Repeat     parm1   parm2   iterno     Repeat      /          curr val
      Negate     parm    /       val
      Not        parm    /       val
      Square     parm    /       val
      Add        parm1   parm2   val
      Subtract   parm1   parm2   val
      Multiply   parm1   parm2   val
      Divide     parm1   parm2   val
      Over       parm    /       val
      Stepper    <See cols to right>
      Reference  refd    /       val
  *)

  (*  Reset   - reloads p.i with first value
      More    - returns whether there are more values available
      Advance - steps p.i to the next value
  *)

TYPE
  Int   = SYSTEM.INT64;
  Ptr   = POINTER TO Obj;
  Obj   = RECORD  kind, i: Int;  p1, p2: Ptr  END;
  OpDef = RECORD  prefix, dyadic, priority: Int  END;

VAR
  Ops:  ARRAY 128 OF OpDef;
  Tree: Ptr;

(* ------------------------------------------------------------------------ *)

PROCEDURE Fail(s: ARRAY OF CHAR);                   BEGIN w.Fail(s)      END Fail;
PROCEDURE Assert(t: BOOLEAN; s: ARRAY [1] OF CHAR); BEGIN w.Assert(t, s) END Assert;

(* ------------------------------------------------------------------------ *)

PROCEDURE NewObj(kind: Int;  p1, p2: Ptr;  i: Int): Ptr;
VAR p: Ptr;
BEGIN Assert(kind # Nobj, "NewObj passed object kind Nobj.");
  NEW(p);
  p.kind := kind;  p.p1 := p1;  p.p2 := p2;  p.i  := i;
RETURN p END NewObj;

PROCEDURE BoolVal(b: BOOLEAN): Int;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE^ Reset(VAR p: Ptr);
PROCEDURE^ Advance(p: Ptr);
PROCEDURE^ More(p: Ptr): BOOLEAN;

PROCEDURE ResetOver(VAR p: Ptr);
BEGIN Reset(p.p1);
  CASE p.p2.kind OF
  |Add:      p.i := p.p1.i; WHILE More(p.p1) DO Advance(p.p1); p.i := p.i  +  p.p1.i END
  |Subtract: p.i := p.p1.i; WHILE More(p.p1) DO Advance(p.p1); p.i := p.i  -  p.p1.i END
  |Multiply: p.i := p.p1.i; WHILE More(p.p1) DO Advance(p.p1); p.i := p.i  *  p.p1.i END
  |Divide:   p.i := p.p1.i; WHILE More(p.p1) DO Advance(p.p1); p.i := p.i DIV p.p1.i END
  |And:      WHILE (p.p1.i # 0) & More(p.p1) DO Advance(p.p1) END; p.i := BoolVal(p.p1.i # 0)
  |Or:       WHILE (p.p1.i = 0) & More(p.p1) DO Advance(p.p1) END; p.i := BoolVal(p.p1.i # 0)
  ELSE       w.Fail("Unsupported over operator.")
  END
END ResetOver;

PROCEDURE PrepareToStep(VAR p: Ptr);
BEGIN IF p.kind <= Repeat THEN p := NewObj(Stepper, p, NIL, 0); Reset(p) END END PrepareToStep;

PROCEDURE MatchPattern(VAR p, k: Ptr);  (* pattern, key *)
BEGIN
  Reset(p);  IF p.kind # Stepper THEN PrepareToStep(p) END;
  Reset(k);  IF k.kind # Stepper THEN PrepareToStep(k) END;
  LOOP
    WHILE (k.i # p.i) & (p.p2.p2 # NIL) DO
      p.p2 := p.p2.p2;  p.i := p.p2.i
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
  MatchPattern(p.p1, p.p2);  (* p1 is pattern, p2 is key. *)
  IF (p.p1.i # p.p2.i) OR More(p.p2) THEN
    p.i := 0                (* No match *)
  ELSIF ~More(p.p1) THEN
    p.i := 1                (* Match but nothing follows *)
  ELSE
    p := p.p1;  Advance(p)  (* Return remaining pattern *)
  END
END ResetMatch;

PROCEDURE ResetMerge(VAR r: Ptr);
VAR p, k: Ptr;  (* Pattern and Key *)
BEGIN
  MatchPattern(r.p1, r.p2);
  r.i := BoolVal((r.p1.i = r.p2.i) & ~More(r.p2));  (* Success iff whole key matched. *)
  IF r.i # 0 THEN r.i := 0 ELSE  (* Fail if already present *)
    (* Insert current pos in p1 as alternate in current pos of p2 *)
    p := r.p1;  k := r.p2;
    w.Assert(p.kind = Stepper,    "Merge expects pattern to be stepper.");
    w.Assert(p.p2.kind = Integer, "Merge expects pattern to reference integer.");
    w.Assert(p.p2.p2 = NIL,       "Merge expects no remaining alternates at mismatch pattern pos.");
    w.Assert(k.kind = Stepper,    "Merge expects key to be stepper.");
    w.Assert(k.p2.kind = Integer, "Merge expects key to reference integer.");
    p.p2.p2 := k.p2;
    r.i := 1
  END
END ResetMerge;

PROCEDURE Evaluate(p: Ptr);
BEGIN CASE p.kind OF
|Negate:     p.i := -p.p1.i
|Not:        p.i := BoolVal(p.p1.i = 0)
|Square:     p.i := p.p1.i  *  p.p1.i
|Add:        p.i := p.p1.i  +  p.p2.i
|Subtract:   p.i := p.p1.i  -  p.p2.i
|Multiply:   p.i := p.p1.i  *  p.p2.i
|Divide:     p.i := p.p1.i DIV p.p2.i
|And:        p.i := BoolVal((p.p1.i # 0) &  (p.p2.i # 0))
|Or:         p.i := BoolVal((p.p1.i # 0) OR (p.p2.i # 0))
|Equal:      p.i := BoolVal(p.p1.i = p.p2.i)
|Reference:  p.i := p.p1.i
ELSE
END END Evaluate;

PROCEDURE Reset(VAR p: Ptr);
BEGIN IF p # NIL THEN CASE p.kind OF
  |Nobj:    Fail("Cannot reset Nobj.")
  |Integer: IF p.p1 # NIL THEN PrepareToStep(p) END
  |Iota:    Reset(p.p1); p.i := p.p1.i; PrepareToStep(p)
  |Repeat:  Reset(p.p2); PrepareToStep(p)
  |Stepper: CASE p.p1.kind OF
            |Integer: p.p2 := p.p1; p.i := p.p1.i
            |Iota:    p.i := 0
            |Repeat:  Reset(p.p1.p1); p.p1.i := 0; p.i := p.p1.p1.i
            ELSE      Fail("Stepper references unsteppable in Reset.")
            END
  |Match:   ResetMatch(p)
  |Merge:   ResetMerge(p)
  |Over:    ResetOver(p)
  ELSE      Reset(p.p1); Reset(p.p2); Evaluate(p)
  END
END END Reset;

PROCEDURE More(p: Ptr): BOOLEAN;
BEGIN IF p # NIL THEN CASE p.kind OF
  |Integer, Repeat, Iota, Match, Merge, Over:
            RETURN FALSE
  |Stepper: (* w.lc; w.s("More on stepper - "); wref(p); w.s(" -> "); wref(p.p1); *)
            CASE p.p1.kind OF
            |Integer: RETURN p.p2.p1 # NIL
            |Iota:    RETURN p.i < p.p1.i-1
            |Repeat:  RETURN (p.p1.i < p.p1.p2.i-1) OR More(p.p1.p1)
            ELSE      Fail("Stepper references unsteppable in More.")
            END
  ELSE      RETURN More(p.p1) OR More(p.p2)
  END
END; RETURN FALSE END More;

PROCEDURE Advance(p: Ptr);
BEGIN IF p # NIL THEN
  CASE p.kind OF
  |Integer, Repeat, Iota, Match, Merge, Over:  (* No action *)
  |Stepper: Assert(More(p), "No more steppable.");
            CASE p.p1.kind OF
            |Integer: p.p2 := p.p2.p1;  p.i := p.p2.i
            |Iota:    INC(p.i)
            |Repeat:  IF More(p.p1.p1) THEN Advance(p.p1.p1);
                      ELSE Reset(p.p1.p1); INC(p.p1.i) END;
                      p.i := p.p1.p1.i
            ELSE      Fail("Stepper references unsteppable in Advance.")
            END
  ELSE      Advance(p.p1); Advance(p.p2); Evaluate(p)
  END
END END Advance;

(* ------------------------------------------------------------------------ *)

PROCEDURE PriorityParse(s: ARRAY OF CHAR): Ptr;
VAR i: Int;

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
    result := NewObj(Integer, NIL, NIL, ParseInt(s, i));  skipSpace;
    IF (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') THEN
      current := result;
      WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
        current.p1 := NewObj(Integer, NIL, NIL, ParseInt(s, i));
        current := current.p1;  skipSpace
      END
    END;
  RETURN result END ParseIntegers;

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

  PROCEDURE ParseChar(delim: CHAR): Int;  (* returns 0 at end *)
  VAR c: Int;
  BEGIN
    IF i >= LEN(s) THEN RETURN 0 END;
    IF s[i] = delim THEN
      INC(i);
      IF (i < LEN(s)) & (s[i] = delim) THEN
        INC(i);  c := ORD(delim)
      ELSE
        c := 0
      END
    ELSE
      c := ParseUTF8()
    END;
  RETURN c END ParseChar;

  PROCEDURE ParseString(): Ptr;
  VAR  result, current: Ptr;  delim: CHAR;  c: Int;
  BEGIN
    delim := s[i]; INC(i);
    c := ParseChar(delim);
    result := NewObj(Integer, NIL, NIL, c);
    IF c # 0 THEN
      current := result;
      c := ParseChar(delim);
      WHILE c # 0 DO
        current.p1 := NewObj(Integer, NIL, NIL, c);
        current := current.p1;
        c := ParseChar(delim);
      END
    END;
  RETURN result END ParseString;

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
               INC(i);  result := NewObj(Over, ParseOperand(), NewObj(op.dyadic,NIL,NIL,0), 0)
    |'0'..'9': result := ParseIntegers()
    |'"',"'":  result := ParseString()
    |'t':      INC(i);  result := Tree;
    ELSE       ParseOperation(op);  INC(i);
               IF op.prefix = Identity THEN result := ParseOperand()
               ELSE result := NewObj(op.prefix, ParseOperand(), NIL, 0) END
    END;
  RETURN result END ParseOperand;


  PROCEDURE ParseDyadic(priority: Int): Ptr;
  VAR  p1: Ptr;  op: OpDef;
  BEGIN  p1 := ParseOperand();
    ParseOperation(op);
    WHILE op.priority >= priority DO
      INC(i);  p1 := NewObj(op.dyadic, p1, ParseDyadic(op.priority+1), 0);
      ParseOperation(op)
    END;
  RETURN p1 END ParseDyadic;

BEGIN i := 0;
  RETURN ParseDyadic(0)
END PriorityParse;


(* ------------------------------------------------------------------------ *)

PROCEDURE Print(p: Ptr);
BEGIN
  Reset(p);  w.i(p.i);  WHILE More(p) DO Advance(p);  w.i(p.i) END
END Print;

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

PROCEDURE TestPriorityParse(ind: Int; s: ARRAY OF CHAR);
VAR i: Int;
BEGIN
  w.s("Pri  "); w.s(s); w.nb; w.s("  ");
  i := ColCount(s);  WHILE i < ind DO w.c(' '); INC(i) END;
  Print(PriorityParse(s)); w.l;
END TestPriorityParse;

(*----------------------------------------------------------------------------

PROCEDURE wkind(k: Int);
BEGIN CASE k OF
|Nobj:     w.s("Nobj")
|Integer:  w.s("Integer")
|Iota:     w.s("Iota")
|Repeat:   w.s("Repeat")
|Negate:   w.s("Negate")
|Not:      w.s("Not")
|Square:   w.s("Square")
|Identity: w.s("Identity")
|Add:      w.s("Add")
|Subtract: w.s("Subtract")
|Multiply: w.s("Multiply")
|Divide:   w.s("Divide")
|Equal:    w.s("Equal")
|Match:    w.s("Match")
|Merge:    w.s("Merge")
|Over:     w.s("Over")
|Stepper:  w.s("Stepper")
ELSE       w.s("Unknown-kind")
END END wkind;

PROCEDURE wref(p: Ptr);
BEGIN
  w.s("Ptr: ");
  IF p = NIL THEN w.sl("NIL.") ELSE
    w.s("kind "); wkind(p.kind);
    w.s(", p1"); IF p.p1 = NIL THEN w.s("NIL") ELSE w.nb; w.s("->"); wkind(p.p1.kind) END;
    w.s(", p2"); IF p.p2 = NIL THEN w.s("NIL") ELSE w.nb; w.s("->"); wkind(p.p2.kind) END;
    w.s(", i "); w.i(p.i);
    w.sl('.')
  END
END wref;

----------------------------------------------------------------------------*)

PROCEDURE Test*;
BEGIN
  TestPriorityParse(18, "1");                 (* 1                       *)
  TestPriorityParse(18, "1+2-(5-1)");         (* -1                      *)
  TestPriorityParse(18, "1-2-3-4");           (* -8                      *)
  TestPriorityParse(18, "2*3+1");             (* 7                       *)
  TestPriorityParse(18, "1+2*3");             (* 7                       *)
  TestPriorityParse(18, "1+2*3+4");           (* 11                      *)
  TestPriorityParse(18, "1 2 3 4");           (* 1 2 3 4                 *)
  TestPriorityParse(18, "1 2 + 3 4");         (* 4 6                     *)
  TestPriorityParse(18, "1 2 3 4 + 10");      (* 11 12 13 14             *)
  TestPriorityParse(18, "i4");                (* 0 1 2 3                 *)
  TestPriorityParse(18, "i4+1");              (* 1 2 3 4                 *)
  TestPriorityParse(18, "1+2*i4");            (* 1 3 5 7                 *)
  TestPriorityParse(18, "1+i4*2");            (* 1 3 5 7                 *)
  TestPriorityParse(18, "1 2 3 4 p 3");       (* 1 2 3 4 1 2 3 4 1 2 3 4 *)
  TestPriorityParse(18, "i4r3");              (* 0 1 2 3 0 1 2 3 0 1 2 3 *)
  TestPriorityParse(18, "/+5");               (* 5                       *)
  TestPriorityParse(18, "/+i5");              (* 10                      *)
  TestPriorityParse(18, "/-i5");              (* -10                     *)
  TestPriorityParse(18, "/*i5");              (* 0                       *)
  TestPriorityParse(18, "/*(i5+1)");          (* 120                     *)
  TestPriorityParse(18, "/+ 5 15 27");        (* 47                      *)
  TestPriorityParse(18, "''");                (* 0                       *)
  TestPriorityParse(18, "'A'");               (* 65                      *)
  TestPriorityParse(18, "'123'");             (* 49 50 51                *)
  TestPriorityParse(18, '"123"');             (* 49 50 51                *)
  TestPriorityParse(18, '"!""#"');            (* 33 34 35                *)
  TestPriorityParse(18, '"¬¦é€£"');           (* 172 166 233 8364 163    *)
  TestPriorityParse(18, "1 2 3 4 = 1 3 2 4"); (* 1 0 0 1                 *)
  TestPriorityParse(18, "'abcde' = 'axcxe'"); (* 1 0 1 0 1               *)
  TestPriorityParse(18, "1 2 3 ? 1 2 3");     (* 1                       *)
  TestPriorityParse(18, "1 2 3 4 ? 1 2");     (* 3 4                     *)
  TestPriorityParse(18, "1 2 3 4 ? 1 9 9 4"); (* 0                       *)
  TestPriorityParse(18, "i4 ? 0 1 2 3");      (* 1                       *)
  TestPriorityParse(18, "0 1 2 3 ? i4");      (* 0                       *)
  TestPriorityParse(18, "'abc' ! 'alpha'");   (* 1                       *)
  TestPriorityParse(18, "'abc' ! 'beta'");    (* 1                       *)
  TestPriorityParse(18, "'abc' ! 'abc'");     (* 0                       *)
  TestPriorityParse(18, "t");                 (* 47                      *)
  TestPriorityParse(18, "t ! 'alpha'");       (* 1                       *)
  TestPriorityParse(18, "t ! 'beta'");        (* 1                       *)
  TestPriorityParse(18, "t ! 'abc'");         (* 1                       *)
  TestPriorityParse(18, "t ! 'abc'");         (* 0                       *)
  TestPriorityParse(18, "t ? 'abc'");         (* 1                       *)
  TestPriorityParse(18, "t ? 'al'");          (* 112 104 97              *)
  TestPriorityParse(18, "t ? 'be'");          (* 116 97                  *)

  Tree := NewObj(Integer, NIL, NIL, ORD('/'));  (* Clear and reset tree so behaviour is repeated *)

  w.l;
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

  DefOp('~', Not,      Nobj,    -1);
  DefOp('i', Iota,     Nobj,    -1);
  DefOp('=', Nobj,     Equal,    0);
  DefOp('?', Nobj,     Match,    0);
  DefOp('!', Nobj,     Merge,    1);
  DefOp('+', Identity, Add,      1);
  DefOp('-', Negate,   Subtract, 1);
  DefOp('*', Nobj,     Multiply, 2);
  DefOp('/', Nobj,     Divide,   2);
  DefOp('&', Nobj,     And,      2);
  DefOp('|', Nobj,     Or,       2);
  DefOp('r', Nobj,     Repeat,   3)
END InitOpLevel;

BEGIN InitOpLevel;  Tree := NewObj(Integer, NIL, NIL, ORD('/'))
END Jobs.


------------------------------------------------------------------------------


PROCEDURE wtree(p: Ptr; nest: Int);
BEGIN
  IF p = NIL THEN w.sl("NIL.") END;
  wkind(p.kind); w.s(" i="); w.nb; w.i(p.i); w.l;
  IF p.p1 # NIL THEN
    w.lc; w.space(nest*4); w.s("p1: "); wtree(p.p1, nest+1)
  END;
  IF p.p2 # NIL THEN
    w.lc; w.space(nest*4); w.s("p2: "); wtree(p.p2, nest+1)
  END;
END wtree;
