MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

(* Vague todos:
   o  Compile. Maybe an IsSingleton fn?
   o  Named value and function definition and invocation
   o  Nested language (and eventually, formatted output)
   o  Distinguish integers and characters just enough
   o  Support partial dyadic operators - where one arg is preset
   o  Less reduction to integer maybe
*)

CONST
  (* Object kinds *)
  Nobj     = 0;                  (* None                                *)
  Integer  = 1;                  (* a singleton integer value           *)
  Iota     = 2;                  (* a vector of 0 up to a limit         *)
  Repeat   = 3;                  (* repeats a source multiple times     *)
  Negate   = 4;   Not      = 5;  (* monadic operators                   *)
  Square   = 6;   Identity = 7;  (* monadic operators                   *)
  Add      = 8;   Subtract = 9;  (* dyadic operators                    *)
  Multiply = 10;  Divide   = 11; (* dyadic operators                    *)
  And      = 12;  Or       = 13; (* dyadic operators                    *)
  Equal    = 14;                 (* returns 0s and 1s                   *)
  Match    = 15;                 (* walk match tree                     *)
  Over     = 16;                 (* Applicator                          *)
  Stepper  = 17;                 (* Steps through algorithmic sequences *)
  ObjLimit = 18;

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
  *)

  (*  Reset   - reloads r.i with first value
      More    - returns whether there are more values available
      Advance - steps r.i to the next value
  *)

TYPE
  Int = SYSTEM.INT64;
  Ref = POINTER TO Obj;
  Obj = RECORD  kind, i: Int;  p1, p2: Ref  END;

VAR
  Ops: ARRAY 128 OF RECORD monadic, dyadic, priority: Int END;

(* ------------------------------------------------------------------------ *)

PROCEDURE Fail(s: ARRAY OF CHAR);                   BEGIN w.Fail(s)      END Fail;
PROCEDURE Assert(t: BOOLEAN; s: ARRAY [1] OF CHAR); BEGIN w.Assert(t, s) END Assert;

(* ------------------------------------------------------------------------ *)

PROCEDURE NewObj(kind: Int;  p1, p2: Ref;  i: Int): Ref;
VAR ref: Ref;
BEGIN Assert(kind # Nobj, "NewObj passed object kind Nobj.");
  NEW(ref);
  ref.kind := kind;  ref.p1 := p1;  ref.p2 := p2;  ref.i  := i;
RETURN ref END NewObj;

PROCEDURE BoolVal(b: BOOLEAN): Int;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE^ Reset(VAR r: Ref);
PROCEDURE^ Advance(r: Ref);
PROCEDURE^ More(r: Ref): BOOLEAN;

PROCEDURE DoOver(VAR r: Ref);
BEGIN Reset(r.p1);
  CASE r.p2.kind OF
  |Add:      r.i := r.p1.i; WHILE More(r.p1) DO Advance(r.p1); r.i := r.i  +  r.p1.i END
  |Subtract: r.i := r.p1.i; WHILE More(r.p1) DO Advance(r.p1); r.i := r.i  -  r.p1.i END
  |Multiply: r.i := r.p1.i; WHILE More(r.p1) DO Advance(r.p1); r.i := r.i  *  r.p1.i END
  |Divide:   r.i := r.p1.i; WHILE More(r.p1) DO Advance(r.p1); r.i := r.i DIV r.p1.i END
  |And:      WHILE (r.p1.i # 0) & More(r.p1) DO Advance(r.p1) END; r.i := BoolVal(r.p1.i # 0)
  |Or:       WHILE (r.p1.i = 0) & More(r.p1) DO Advance(r.p1) END; r.i := BoolVal(r.p1.i # 0)
  ELSE       w.Fail("Unsupported over operator.")
  END
END DoOver;

PROCEDURE DoMatch(VAR r: Ref);
VAR k, p: Ref;  (* Key and Pattern *)
BEGIN
  Reset(r.p1);  k := r.p1;
  Reset(r.p2);  p := r.p2;
  r.i := 0;  (* No match by default *)
  LOOP
    WHILE (k.i # p.i) & (p.kind = Stepper) & (p.p2.kind = Integer) & (p.p2.p2 # NIL) DO
      r.p2 := r.p2.p2
    END;
    IF More(k) & More(p) & (k.i = p.i) THEN
      Advance(k); Advance(p)
    ELSE
      EXIT
    END
  END;
  r.i := BoolVal((k.i = p.i) & ~More(k))  (* Success iff whole key matched. *)
END DoMatch;

PROCEDURE Evaluate(r: Ref);
BEGIN CASE r.kind OF
|Negate:   r.i := -r.p1.i
|Not:      r.i := BoolVal(r.p1.i = 0)
|Square:   r.i := r.p1.i  *  r.p1.i
|Add:      r.i := r.p1.i  +  r.p2.i
|Subtract: r.i := r.p1.i  -  r.p2.i
|Multiply: r.i := r.p1.i  *  r.p2.i
|Divide:   r.i := r.p1.i DIV r.p2.i
|And:      r.i := BoolVal((r.p1.i # 0) &  (r.p2.i # 0))
|Or:       r.i := BoolVal((r.p1.i # 0) OR (r.p2.i # 0))
|Equal:    r.i := BoolVal(r.p1.i = r.p2.i)
ELSE
END END Evaluate;

PROCEDURE SetStepper(VAR r: Ref);
BEGIN r := NewObj(Stepper, r, NIL, 0); Reset(r) END SetStepper;

PROCEDURE Reset(VAR r: Ref);
BEGIN IF r # NIL THEN CASE r.kind OF
  |Nobj:    Fail("Cannot reset Nobj.")
  |Integer: IF r.p1 # NIL THEN SetStepper(r) END
  |Iota:    Reset(r.p1); r.i := r.p1.i; SetStepper(r)
  |Repeat:  Reset(r.p2); SetStepper(r)
  |Stepper: CASE r.p1.kind OF
            |Integer: r.p2 := r.p1; r.i := r.p1.i
            |Iota:    r.i := 0
            |Repeat:  Reset(r.p1.p1); r.p1.i := 0; r.i := r.p1.p1.i
            ELSE      Fail("Stepper references unsteppable in Reset.")
            END
  |Match:   DoMatch(r)
  |Over:    DoOver(r)
  ELSE      Reset(r.p1); Reset(r.p2); Evaluate(r)
  END
END END Reset;

PROCEDURE More(r: Ref): BOOLEAN;
BEGIN IF r # NIL THEN CASE r.kind OF
  |Integer, Repeat, Iota, Match, Over:
            RETURN FALSE
  |Stepper: (* w.lc; w.s("More on stepper - "); wref(r); w.s(" -> "); wref(r.p1); *)
            CASE r.p1.kind OF
            |Integer: RETURN r.p2.p1 # NIL
            |Iota:    RETURN r.i < r.p1.i-1
            |Repeat:  RETURN (r.p1.i < r.p1.p2.i-1) OR More(r.p1.p1)
            ELSE      Fail("Stepper references unsteppable in More.")
            END
  ELSE      RETURN More(r.p1) OR More(r.p2)
  END
END; RETURN FALSE END More;

PROCEDURE Advance(r: Ref);
BEGIN IF r # NIL THEN
  CASE r.kind OF
  |Integer, Repeat, Iota, Match, Over:  (* No action *)
  |Stepper: Assert(More(r), "No more steppable.");
            CASE r.p1.kind OF
            |Integer: r.p2 := r.p2.p1;  r.i := r.p2.i
            |Iota:    INC(r.i)
            |Repeat:  IF More(r.p1.p1) THEN Advance(r.p1.p1);
                      ELSE Reset(r.p1.p1); INC(r.p1.i) END;
                      r.i := r.p1.p1.i
            ELSE      Fail("Stepper references unsteppable in Advance.")
            END
  ELSE      Advance(r.p1); Advance(r.p2); Evaluate(r)
  END
END END Advance;

(* ------------------------------------------------------------------------ *)

PROCEDURE PriorityParse(s: ARRAY OF CHAR): Ref;
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

  PROCEDURE ParseIntegers(): Ref;
  VAR result, current: Ref;
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

  PROCEDURE ParseChar(delim: CHAR): Int;  (* returns 0 at end *)
  VAR c, n: Int;
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
      c := ORD(s[i]);  INC(i);
      IF (i < LEN(s)) & (c >= 128) THEN (* Multi-byte UTF-8 encoding *)
        IF    (c DIV 32) =  6 THEN c := c MOD 32;  n := 2
        ELSIF (c DIV 16) = 14 THEN c := c MOD 16;  n := 3
        ELSIF (c DIV  8) = 30 THEN c := c MOD  8;  n := 4
        ELSE  c := 0FFFDH (* Unicode replacement character *)
        END;
        IF c < 32 THEN
          WHILE (i < LEN(s)) & (n > 1) & (ORD(s[i]) >= 128) & (ORD(s[i]) < 192) DO
            c := c * 64  +  ORD(s[i]) MOD 64;  INC(i);  DEC(n)
          END;
          IF n # 1 THEN c := 0FFFDH END
        END
      END
    END;
  RETURN c END ParseChar;

  PROCEDURE ParseString(): Ref;
  VAR  result, current: Ref;  delim: CHAR;  c: Int;
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

  PROCEDURE^ ParseDyadic(priority: Int): Ref;

  PROCEDURE ParseOperand(): Ref;
  VAR  result, link: Ref;  op, val: Int;
  BEGIN skipSpace;
    CASE s[i] OF
    |'(':      INC(i);  result := ParseDyadic(0);  skipSpace;  expect(')')
    |'/':      INC(i);  skipSpace;  op := Ops[ORD(s[i])].dyadic;
               Assert(op # Nobj, "Expected dyadic operator following '/'.");
               INC(i);  result := NewObj(Over, ParseOperand(), NewObj(op,NIL,NIL,0), op)
    |'0'..'9': result := ParseIntegers()
    |'"',"'":  result := ParseString()
    ELSE       op := Ops[ORD(s[i])].monadic;  INC(i);
               IF op = Identity THEN result := ParseOperand()
               ELSE result := NewObj(op, ParseOperand(), NIL, 0) END
    END;
  RETURN result END ParseOperand;

  PROCEDURE ParseDyadic(priority: Int): Ref;
  VAR  p1: Ref;  c: Int;
  BEGIN  p1 := ParseOperand();
    LOOP
      skipSpace;  c := ORD(s[i]);
      IF Ops[c].priority < priority THEN EXIT END;
      INC(i);  p1 := NewObj(Ops[c].dyadic, p1, ParseDyadic(Ops[c].priority+1), 0)
    END;
  RETURN p1 END ParseDyadic;

BEGIN i := 0;
  RETURN ParseDyadic(0)
END PriorityParse;


(* ------------------------------------------------------------------------ *)

PROCEDURE Print(r: Ref);
BEGIN
  Reset(r);  w.i(r.i);  WHILE More(r) DO Advance(r);  w.i(r.i) END
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

PROCEDURE Test*;
BEGIN
  TestPriorityParse(18, "1");                 (* 1                       *)
  TestPriorityParse(18, "1+2-(5-1)");         (* -1                      *)
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
  TestPriorityParse(18, "1 2 3 4 r 3");       (* 1 2 3 4 1 2 3 4 1 2 3 4 *)
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
  TestPriorityParse(18, "1 2 3 4 ? 1 9 9 4"); (* 0                       *)
  w.l;
  TestPriorityParse(50, "/&( 1                 = 1 )");
  TestPriorityParse(50, "/&( 1+2-(5-1)         = -1 )");
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

END Test;


(* ------------------------------------------------------------------------ *)

PROCEDURE DefOp(c: CHAR; monadic, dyadic, priority: Int);
BEGIN
  Ops[ORD(c)].monadic  := monadic;
  Ops[ORD(c)].dyadic   := dyadic;
  Ops[ORD(c)].priority := priority
END DefOp;

PROCEDURE InitOpLevel;
VAR i: Int;
BEGIN
  FOR i := 0 TO 127 DO
    Ops[i].monadic  := Nobj;
    Ops[i].dyadic   := Nobj;
    Ops[i].priority := -1
  END;

  DefOp('~', Not,      Nobj,     -1);
  DefOp('i', Iota,     Nobj,     -1);
  DefOp('=', Nobj,     Equal,    0);
  DefOp('?', Nobj,     Match,    0);
  DefOp('+', Identity, Add,      1);
  DefOp('-', Negate,   Subtract, 1);
  DefOp('*', Nobj,     Multiply, 2);
  DefOp('/', Nobj,     Divide,   2);
  DefOp('&', Nobj,     And,      2);
  DefOp('|', Nobj,     Or,       2);
  DefOp('r', Nobj,     Repeat,   3)
END InitOpLevel;

BEGIN InitOpLevel
END Jobs.


------------------------------------------------------------------------------

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
|Over:     w.s("Over")
|Stepper:  w.s("Stepper")
ELSE       w.s("Unknown-kind")
END END wkind;

PROCEDURE wref(r: Ref);
BEGIN
  w.s("Ref: ");
  IF r = NIL THEN w.sl("NIL.") ELSE
    w.s("kind "); wkind(r.kind);
    w.s(", p1"); IF r.p1 = NIL THEN w.s("NIL") ELSE w.nb; w.s("->"); wkind(r.p1.kind) END;
    w.s(", p2"); IF r.p2 = NIL THEN w.s("NIL") ELSE w.nb; w.s("->"); wkind(r.p2.kind) END;
    w.s(", i "); w.i(r.i);
    w.sl('.')
  END
END wref;

PROCEDURE wtree(r: Ref; nest: Int);
BEGIN
  IF r = NIL THEN w.sl("NIL.") END;
  wkind(r.kind); w.s(" i="); w.nb; w.i(r.i); w.l;
  IF r.p1 # NIL THEN
    w.lc; w.space(nest*4); w.s("p1: "); wtree(r.p1, nest+1)
  END;
  IF r.p2 # NIL THEN
    w.lc; w.space(nest*4); w.s("p2: "); wtree(r.p2, nest+1)
  END;
END wtree;

------------------------------------------------------------------------------

aMatch     = POINTER TO Match;      Match     = RECORD (Obj) next, alt: aMatch       END;
aNonLetter = POINTER TO NonLetter;  NonLetter = RECORD (Match)                       END;
aCharMatch = POINTER TO CharMatch;  CharMatch = RECORD (Match) ch: Int               END;
aPattern   = POINTER TO Pattern;    Pattern   = RECORD (Obj) first, cur: Ref         END;

PROCEDURE (VAR m: Match)     Matches(c: Int): BOOLEAN; BEGIN w.Fail("Abstract Match.Matches() called.") END Matches;
PROCEDURE (VAR m: CharMatch) Matches(c: Int): BOOLEAN; BEGIN RETURN c = m.ch                END Matches;
PROCEDURE (VAR m: NonLetter) Matches(c: Int): BOOLEAN;
BEGIN RETURN  (c < ORD('A'))
          OR  (c > ORD('z'))
          OR ((c > ORD('Z')) & (c < ORD('a'))) END Matches;

PROCEDURE (VAR p: Pattern) Reset;            BEGIN p.cur := p.first                         END Reset;
PROCEDURE (VAR p: Pattern) Val():  Int;      BEGIN RETURN p.cur(aCharMatch).ch              END Val;
PROCEDURE (VAR p: Pattern) Init(m: aMatch);  BEGIN p.first := m; p.Reset                    END Init;
PROCEDURE (VAR p: Pattern) IsMatch(): BOOLEAN;       BEGIN RETURN p.cur IS aMatch           END IsMatch;
PROCEDURE (VAR p: Pattern) Matches(c: Int): BOOLEAN; BEGIN RETURN p.cur(aMatch).Matches(c)  END Matches;

PROCEDURE (VAR p: Pattern) More(): BOOLEAN;
BEGIN RETURN (p.cur IS aMatch) & (p.cur(aMatch).next # NIL) END More;

PROCEDURE (VAR p: Pattern) Advance;
BEGIN IF More(p) THEN p.cur := p.cur(aMatch).next END END Advance;

PROCEDURE (VAR p: Pattern) HasAlt(): BOOLEAN;
BEGIN RETURN (p.cur IS aMatch) & (p.cur(aMatch).alt # NIL) END HasAlt;

PROCEDURE (VAR p: Pattern) Alt;
BEGIN p.cur := p.cur(aMatch).alt END Alt;

PROCEDURE Lookup(s: ARRAY [1] OF CHAR; beg, end: Int; n: aMatch);
VAR i: Int; p: Pattern;
BEGIN
  i := beg;  p.Init(n);
  LOOP
    IF i >= end THEN w.sl("Lookup reached end of string."); EXIT END;
    IF p.IsMatch() THEN
      IF p.Matches(ORD(s[i])) THEN
        IF More(p) THEN
          INC(i); Advance(p)
        ELSE
          w.sl("Lookup matched character but no more in sequence."); EXIT
        END
      ELSE
        IF p.HasAlt() THEN
          p.Alt
        ELSE
          w.sl("Lookup failed to match character and no alternative."); EXIT
        END
      END
    ELSE
      w.sl("Lookup reached non-match node."); EXIT
    END
  END
END Lookup;

PROCEDURE TestMatch;
VAR r, n: aMatch;  cn: aCharMatch;  nl: aNonLetter;
BEGIN
  NEW(cn); cn.ch := ORD('M');  r := cn;       n := cn;
  NEW(cn); cn.ch := ORD('r');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('D');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('U');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('L');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('E');  n.next := cn;  n := cn;
  NEW(nl);                     n.next := nl;  n := nl;

  Lookup("MODULE fred;", 0, 12, r);
  Lookup("MUDDY", 0, 5, r);
  Lookup("MOD", 0, 3, r);
END TestMatch;
