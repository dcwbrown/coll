MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

(* Vague todos:
   o  Match shouldn't be a special case for singleton results in More/Advance
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
  Equal    = 12;                 (* returns 0s and 1s                   *)
  Match    = 13;                 (* walk match tree                     *)
  Over     = 14;                 (* Applicator                          *)
  Stepper  = 15;                 (* Steps through algorithmic sequences *)
  ObjLimit = 16;

  (*

  ============ object ============      =========== stepper ============
  Kind       p1      p2      i          p1          p2         i
  --------   -----   -----   -----      ---------   --------   ---------
  Integer    next    /       value      first int   curr int   /
  Iota       parm    /       max        Iota        /          curr val
  Repeat     parm1   parm2   max        Repeat      /          curr iter
  Negate     parm    /       /
  Not        parm    /       /
  Square     parm    /       /
  Add        parm1   parm2   /
  Subtract   parm1   parm2   /
  Multiply   parm1   parm2   /
  Divide     parm1   parm2   /
  Over       parm    /       op
  Stepper    <See cols to right>
  *)

  (* Special integer value placeholder for lazy evaluation *)
  Pending = MIN(SYSTEM.INT64);

TYPE
  Int = SYSTEM.INT64;
  Ref = POINTER TO Obj;
  Obj = RECORD  kind: Int;  p1, p2: Ref;  i: Int  END;

VAR
  OpLevel: ARRAY ObjLimit OF Int;
  Operators: ARRAY 128 OF RECORD monadic, dyadic: Int END;

PROCEDURE Fail(s: ARRAY OF CHAR);                   BEGIN w.Fail(s)      END Fail;
PROCEDURE Assert(t: BOOLEAN; s: ARRAY [1] OF CHAR); BEGIN w.Assert(t, s) END Assert;

PROCEDURE^ DoOver(VAR r: Ref): Int;
PROCEDURE^ DoMatch(VAR r: Ref);

PROCEDURE Value(r: Ref): Int;
BEGIN CASE r.kind OF
|Integer:  RETURN r.i
|Negate:   RETURN -Value(r.p1)
|Not:      IF Value(r.p1) = 0 THEN RETURN 1 ELSE RETURN 0 END
|Square:   RETURN Value(r.p1)  *  Value(r.p1)
|Add:      RETURN Value(r.p1)  +  Value(r.p2)
|Subtract: RETURN Value(r.p1)  -  Value(r.p2)
|Multiply: RETURN Value(r.p1)  *  Value(r.p2)
|Divide:   RETURN Value(r.p1) DIV Value(r.p2)
|Equal:    IF Value(r.p1) = Value(r.p2) THEN RETURN 1 ELSE RETURN 0 END
|Match:    IF r.i = Pending THEN DoMatch(r) END; RETURN r.i
|Over:     RETURN DoOver(r);
|Stepper:  CASE r.p1.kind OF
           |Integer:  RETURN r.p2.i
           |Iota:     RETURN r.i
           |Repeat:   RETURN Value(r.p1.p1)
           ELSE       w.Fail("Stepper linked to unsteppable.");
           END
ELSE w.Fail("Value() passed unexpected object kind.")
END END Value;

PROCEDURE Reset(r: Ref);
BEGIN IF r # NIL THEN
  IF r.kind # Stepper THEN Reset(r.p1); Reset(r.p2)
  ELSE
    CASE r.p1.kind OF
    |Integer:  r.p2 := r.p1
    |Iota:     IF r.p1.i = Pending THEN r.p1.i := Value(r.p1.p1)-1 END;
               r.i := 0;
    |Repeat:   IF r.p1.i = Pending THEN r.p1.i := Value(r.p1.p2)-1 END;
               Reset(r.p1.p1);  r.i := 0
    ELSE
    END
  END
END END Reset;

PROCEDURE More(r: Ref): BOOLEAN;
BEGIN IF r # NIL THEN
IF      r.kind = Match   THEN RETURN FALSE
  ELSIF r.kind # Stepper THEN RETURN More(r.p1) OR More(r.p2)
  ELSE
    CASE r.p1.kind OF
    |Integer:  RETURN r.p2.p1 # NIL
    |Iota:     Assert(r.p1.i # Pending, "More called with iota stepper p1.i unexpectedly pending, Reset should have been called first.");
               RETURN r.i < r.p1.i
    |Repeat:   Assert(r.p1.i # Pending, "More called with repeat stepper p1.i unexpectedly pending, Reset should have been called first.");
               RETURN (r.i < r.p1.i) OR More(r.p1)
    ELSE       w.Fail("Stepper linked to unsteppable.");
    END
  END
END; RETURN FALSE END More;

PROCEDURE Advance(r: Ref);
BEGIN IF (r # NIL) & (r.kind # Match) THEN
  IF r.kind # Stepper THEN Advance(r.p1); Advance(r.p2)
  ELSE
    CASE r.p1.kind OF
    |Integer:  IF r.p2.p1 # NIL THEN r.p2 := r.p2.p1 END
    |Iota:     Assert(r.p1.i # Pending, "Advance called with iota stepper p1.i unexpectedly pending, Reset should have been called first.");
               IF r.i < r.p1.i THEN INC(r.i) END
    |Repeat:   Assert(r.p1.i # Pending, "Advance called with repeat stepper p1.i unexpectedly pending, Reset should have been called first.");
               IF More(r.p1) THEN
                 Advance(r.p1)
               ELSIF r.i < r.p1.i THEN
                 Reset(r.p1);  INC(r.i)
               END
    ELSE
    END
  END
END END Advance;

(* Patterns use integer.p2 as alternative pointer *)
PROCEDURE HasAlternative(r: Ref): BOOLEAN;
BEGIN RETURN (r.kind = Stepper) & (r.p2 # NIL) & (r.p2.kind = Integer) & (r.p2.p2 # NIL)
END HasAlternative;

PROCEDURE TakeAlternative(r: Ref);
BEGIN IF HasAlternative(r) THEN r.p2 := r.p2.p2 END
END TakeAlternative;

PROCEDURE DoOver(VAR r: Ref): Int;
(* TODO DoOver needs to support applying any dyadic fn, including user defined. *)
VAR acc: Int;
BEGIN Reset(r.p1);  acc := Value(r.p1);
  CASE r.i OF
  |Add:      WHILE More(r.p1) DO Advance(r.p1); acc := acc  +  Value(r.p1) END
  |Subtract: WHILE More(r.p1) DO Advance(r.p1); acc := acc  -  Value(r.p1) END
  |Multiply: WHILE More(r.p1) DO Advance(r.p1); acc := acc  *  Value(r.p1) END
  |Divide:   WHILE More(r.p1) DO Advance(r.p1); acc := acc DIV Value(r.p1) END
  ELSE w.Fail("Unsupported over operator.")
  END;
  RETURN acc;
END DoOver;

PROCEDURE DoMatch(VAR r: Ref);
VAR k, p: Ref;  (* Key and Pattern *)  result: Int;
BEGIN  k := r.p1;  p := r.p2;
  r.i := 0;  (* No match by default *)
  LOOP
    WHILE (Value(k) # Value(p)) & HasAlternative(p) DO TakeAlternative(p) END;
    IF More(k) & More(p) & (Value(k) = Value(p)) THEN
      Advance(k); Advance(p)
    ELSE
      EXIT
    END
  END;
  (* Success iff whole key matched. *)
  IF (Value(k) = Value(p)) & ~More(k) THEN r.i := 1 END
END DoMatch;

PROCEDURE NewObj(kind: Int; p1, p2: Ref; i: Int): Ref;
VAR ref: Ref;
BEGIN Assert(kind # Nobj, "NewObj passed object kinf Nobj.");
  NEW(ref);
  ref.kind := kind;  ref.p1 := p1;  ref.p2 := p2;  ref.i  := i;
RETURN ref END NewObj;

PROCEDURE NewOperator(op: Int; p1, p2: Ref): Ref;
VAR result: Ref;
BEGIN
  IF (op = Nobj) OR (op = Identity) THEN result := p1
  ELSE result := NewObj(op, p1, p2, Pending)
  END;
  CASE op OF
  |Iota, Repeat: result := NewObj(Stepper, result, NIL, 0)
  ELSE
  END;
RETURN result END NewOperator;

PROCEDURE ParseInt(VAR s: ARRAY OF CHAR; VAR i: Int): Int;
VAR acc: Int;
BEGIN acc := 0;
  WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
    acc := acc*10 + ORD(s[i]) - ORD('0');  INC(i)
  END;
RETURN acc END ParseInt;


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

  PROCEDURE ParseIntegers(): Ref;
  VAR result, current: Ref;
  BEGIN
    result := NewObj(Integer, NIL, NIL, ParseInt(s, i));  skipSpace;
    IF (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') THEN
      current := result;  result := NewObj(Stepper, current, current, 0);
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
      current := result;  result := NewObj(Stepper, current, current, 0);
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
    |'/':      INC(i);  skipSpace;  op := Operators[ORD(s[i])].dyadic;
               Assert(op # Nobj, "Expected dyadic operator following '/'.");
               INC(i);  result := NewObj(Over, ParseOperand(), NIL, op)
    |'0'..'9': result := ParseIntegers()
    |'"',"'":  result := ParseString()
    ELSE       op := Operators[ORD(s[i])].monadic;
               Assert(op # Nobj, "Nothing suitable for ParseOperand.");
               INC(i);  result := NewOperator(op, ParseOperand(), NIL)
    END;
  RETURN result END ParseOperand;

  PROCEDURE ParseDyadic(priority: Int): Ref;
  VAR  op: Int;  p1: Ref;
  BEGIN  p1 := ParseOperand();
    LOOP
      skipSpace;  op := Operators[ORD(s[i])].dyadic;
      IF OpLevel[op] < priority THEN EXIT END;
      INC(i);  p1 := NewOperator(op, p1, ParseDyadic(OpLevel[op]+1))
    END;
  RETURN p1 END ParseDyadic;

BEGIN i := 0;
  RETURN ParseDyadic(0)
END PriorityParse;


(* ------------------------------------------------------------------------ *)

PROCEDURE Print(r: Ref);
BEGIN  Reset(r);  w.i(Value(r));
  WHILE More(r) DO Advance(r); w.i(Value(r)) END
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

PROCEDURE TestPriorityParse(s: ARRAY OF CHAR);
VAR i: Int;
BEGIN
  w.s("Pri  "); w.s(s); w.nb; w.s("  ");
  i := ColCount(s);  WHILE i < 18 DO w.c(' '); INC(i) END;
  Print(PriorityParse(s)); w.l;
END TestPriorityParse;

PROCEDURE Test*;
BEGIN
  TestPriorityParse("1+2-(5-1)");         (* -1                      *)
  TestPriorityParse("2*3+1");             (* 7                       *)
  TestPriorityParse("1+2*3");             (* 7                       *)
  TestPriorityParse("1+2*3+4");           (* 11                      *)
  TestPriorityParse("1+2*i4");            (* 1 3 5 7                 *)
  TestPriorityParse("1+i4*2");            (* 1 3 5 7                 *)
  TestPriorityParse("i4r3");              (* 0 1 2 3 0 1 2 3 0 1 2 3 *)
  TestPriorityParse("/+5");               (* 5                       *)
  TestPriorityParse("/+i5");              (* 10                      *)
  TestPriorityParse("/-i5");              (* -10                     *)
  TestPriorityParse("/*i5");              (* 0                       *)
  TestPriorityParse("/*(i5+1)");          (* 120                     *)
  TestPriorityParse("1 2 3 4");           (* 1 2 3 4                 *)
  TestPriorityParse("1 2 3 4 r 3");       (* 1 2 3 4 1 2 3 4 1 2 3 4 *)
  TestPriorityParse("1 2 3 4 + 10");      (* 11 12 13 14             *)
  TestPriorityParse("/+ 5 15 27");        (* 47                      *)
  TestPriorityParse("''");                (* 0                       *)
  TestPriorityParse("'A'");               (*                         *)
  TestPriorityParse("'123'");             (* 49 50 51                *)
  TestPriorityParse('"123"');             (* 49 50 51                *)
  TestPriorityParse('"!""#"');            (* 33 34 35                *)
  TestPriorityParse('"¬¦é€£"');           (* 172 166 233 8364 163    *)
  TestPriorityParse("1 2 3 4 = 1 3 2 4"); (* 1 0 0 1                 *)
  TestPriorityParse("'abcde' = 'axcxe'"); (* 1 0 1 0 1               *)
  TestPriorityParse("1 2 3 ? 1 2 3");     (* 1                       *)
  TestPriorityParse("1 2 3 4 ? 1 9 9 4"); (* 0                       *)

END Test;


(* ------------------------------------------------------------------------ *)

PROCEDURE InitOpLevel;
VAR i: Int;
BEGIN FOR i := 0 TO ObjLimit-1 DO OpLevel[i] := 0 END;
  OpLevel[Nobj]     := -1;
  OpLevel[Multiply] := 1;
  OpLevel[Divide]   := 1;
  OpLevel[Repeat]   := 2;

  FOR i := 0 TO 127 DO
    Operators[i].monadic := Nobj;
    Operators[i].dyadic  := Nobj
  END;

  Operators[ORD('+')].monadic := Identity;  Operators[ORD('-')].monadic := Negate;
  Operators[ORD('~')].monadic := Not;       Operators[ORD('i')].monadic := Iota;

  Operators[ORD('+')].dyadic := Add;        Operators[ORD('-')].dyadic := Subtract;
  Operators[ORD('*')].dyadic := Multiply;   Operators[ORD('/')].dyadic := Divide;
  Operators[ORD('=')].dyadic := Equal;      Operators[ORD('r')].dyadic := Repeat;
  Operators[ORD('?')].dyadic := Match;
END InitOpLevel;

BEGIN InitOpLevel
END Jobs.


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
