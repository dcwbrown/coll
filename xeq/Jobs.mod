MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

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
  Over     = 12;                 (* Applicator                          *)
  Stepper  = 13;                 (* Steps through algorithmic sequences *)
  ObjLimit = 14;

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
  Stepper    parm    <See sep cols>
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


PROCEDURE^ DoOver(VAR r: Ref): Int;

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
|Over:     RETURN DoOver(r);
|Stepper:  CASE r.p1.kind OF
           |Integer:  RETURN Value(r.p2)
           |Iota:     RETURN r.i
           |Repeat:   RETURN Value(r.p1.p1)
           ELSE       w.Fail("Stepper linked to unsteppable.");
           END
ELSE w.Fail("Value() passed unexpected object kind.")
END END Value;

PROCEDURE Reset(r: Ref);
BEGIN IF r # NIL THEN
  IF r.kind = Stepper THEN
    CASE r.p1.kind OF
    |Integer:  r.p2 := r.p1
    |Iota:     IF r.p1.i = Pending THEN r.p1.i := Value(r.p1.p1)-1 END;
               r.i := 0;
    |Repeat:   IF r.p1.i = Pending THEN r.p1.i := Value(r.p1.p2)-1 END;
               Reset(r.p1.p1);  r.i := 0
    ELSE
    END
  ELSE
    Reset(r.p1);  Reset(r.p2);
  END
END END Reset;

PROCEDURE More(r: Ref): BOOLEAN;
BEGIN
  IF r # NIL THEN
    IF r.kind # Stepper THEN
      RETURN More(r.p1) OR More(r.p2)
    ELSE
      CASE r.p1.kind OF
      |Integer:  RETURN r.p2.p1 # NIL
      |Iota:     w.Assert(r.p1.i # Pending, "More called with iota stepper p1.i unexpectedly pending, Reset should have been called first.");
                 RETURN r.i < r.p1.i
      |Repeat:   w.Assert(r.p1.i # Pending, "More called with repeat stepper p1.i unexpectedly pending, Reset should have been called first.");
                 RETURN (r.i < r.p1.i) OR More(r.p1)
      ELSE       w.Fail("Stepper linked to unsteppable.");
      END
    END
  END;
RETURN FALSE END More;

PROCEDURE Advance(r: Ref);
BEGIN
  IF r.kind # Stepper THEN
    IF More(r.p1)  THEN Advance(r.p1)  END;
    IF More(r.p2) THEN Advance(r.p2) END
  ELSE
    CASE r.p1.kind OF
    |Integer:  IF r.p2.p1 # NIL THEN r.p2 := r.p2.p1 END
    |Iota:     w.Assert(r.p1.i # Pending, "Advance called with iota stepper p1.i unexpectedly pending, Reset should have been called first.");
               IF r.i < r.p1.i THEN INC(r.i) END
    |Repeat:   w.Assert(r.p1.i # Pending, "Advance called with repeat stepper p1.i unexpectedly pending, Reset should have been called first.");
               IF More(r.p1) THEN
                 Advance(r.p1)
               ELSIF r.i < r.p1.i THEN
                 Reset(r.p1);  INC(r.i)
               END
    ELSE
    END
  END
END Advance;

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

PROCEDURE NewObj(kind: Int; p1, p2: Ref; i: Int): Ref;
VAR ref: Ref;
BEGIN w.Assert(kind # Nobj, "NewObj passed object kinf Nobj.");
  NEW(ref);
  ref.kind := kind;  ref.p1 := p1;  ref.p2 := p2;  ref.i  := i;
RETURN ref END NewObj;

PROCEDURE NewOperator(op: Int; p1, p2: Ref): Ref;
BEGIN CASE op OF
|Nobj, Identity:
           RETURN p1
|Iota:     RETURN NewObj(Stepper, NewObj(Iota,   p1, NIL, Pending), NIL, 0)
|Repeat:   RETURN NewObj(Stepper, NewObj(Repeat, p1,  p2, Pending), NIL, 0)
|Negate, Not, Add, Subtract, Multiply, Divide:
           RETURN NewObj(op, p1, p2, 0)
ELSE w.Fail("Unrecognised operator in NewOperator.")
END END NewOperator;

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
    w.Assert(s[i] = c, "Unexpected character in PriorityParse");
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

  PROCEDURE^ ParseDyadic(priority: Int): Ref;

  PROCEDURE ParseOperand(): Ref;
  VAR  result, link: Ref;  op, val: Int;
  BEGIN skipSpace;
    CASE s[i] OF
    |'(':      INC(i);  result := ParseDyadic(0);  skipSpace;  expect(')')
    |'/':      INC(i);  skipSpace;  op := Operators[ORD(s[i])].dyadic;
               w.Assert(op # Nobj, "Expected dyadic operator following '/'.");
               INC(i);  result := NewObj(Over, ParseOperand(), NIL, op)
    |'0'..'9': result := ParseIntegers()
    ELSE       op := Operators[ORD(s[i])].monadic;
               w.Assert(op # Nobj, "Nothing suitable for ParseOperand.");
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

PROCEDURE RpnParse(s: ARRAY OF CHAR): Ref;
VAR r: Ref;  v, i, top: Int;  stk: ARRAY 3 OF Ref;

  PROCEDURE Push(r: Ref); BEGIN INC(top);  stk[top] := r    END Push;
  PROCEDURE Pop(): Ref;   BEGIN DEC(top); RETURN stk[top+1] END Pop;

BEGIN i := 0;  top := -1;
  WHILE i < LEN(s) DO
    IF (s[i] >= '0') & (s[i] <= '9') THEN
      Push(NewObj(Integer, NIL, NIL, ParseInt(s, i)))
    ELSE
      CASE s[i] OF
      |'n': Push(NewObj(Negate,   Pop(), NIL,   0))
      |'~': Push(NewObj(Not,      Pop(), NIL,   0))
      |'s': Push(NewObj(Square,   Pop(), NIL,   0))
      |'+': Push(NewObj(Add,      Pop(), Pop(), 0))
      |'-': Push(NewObj(Subtract, Pop(), Pop(), 0))
      |'*': Push(NewObj(Multiply, Pop(), Pop(), 0))
      |'/': Push(NewObj(Divide,   Pop(), Pop(), 0))
      |'#': r := Pop();
            Push(NewObj(Stepper, NewObj(Repeat, Pop(), r, Pending), NIL, 0))
      |'i': Push(NewObj(Stepper, NewObj(Iota, Pop(), NIL, Pending), NIL, 0))
      |' ', 00X:
      ELSE  w.s("Unexpected character '"); w.c(s[i]); w.s("' in RpnParse input."); w.Fail('');
      END;
      INC(i)
    END
  END;
  w.Assert(top = 0, "Stack does not have single entry at RpnParse completion.");
  RETURN stk[top]
END RpnParse;


(* ------------------------------------------------------------------------ *)

PROCEDURE Print(r: Ref);
BEGIN  Reset(r);  w.i(Value(r));
  WHILE More(r) DO Advance(r); w.i(Value(r)) END
END Print;

PROCEDURE StringLength(s: ARRAY [1] OF CHAR): Int;
VAR i: Int;
BEGIN i := 0;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO INC(i) END;
RETURN i END StringLength;

PROCEDURE TestRpnParse(s: ARRAY OF CHAR);
VAR i: Int;
BEGIN
  w.s("Rpn  "); w.s(s); w.nb; w.s("  ");
  i := StringLength(s);  WHILE i < 18 DO w.c(' '); INC(i) END;
  Print(RpnParse(s)); w.l;
END TestRpnParse;

PROCEDURE RpnTest;
VAR r: Ref;
BEGIN
  TestRpnParse("10");                (* 10                           *)
  TestRpnParse("2");                 (* 2                            *)
  TestRpnParse("10 2 +");            (* 12                           *)
  TestRpnParse("5i");                (* 0 1 2 3 4                    *)
  TestRpnParse("5i 2 +");            (* 2 3 4 5 6                    *)
  TestRpnParse("1 2 #");             (* 1 1                          *)
  TestRpnParse("3 4 + 2 #");         (* 7 7                          *)
  TestRpnParse("5i 2#");             (* 0 1 2 3 4 0 1 2 3 4          *)
  TestRpnParse("10 8# 5i +");        (* 10 11 12 13 14 14 14 14      *)
  TestRpnParse("9i 10*");            (* 0 10 20 30 40 50 60 70 80    *)
  TestRpnParse("9i 10* 10+");        (* 10 20 30 40 50 60 70 80 90   *)
  TestRpnParse("6i 9i 10* 10+ +");   (* 10 21 32 43 54 65 75 85 95   *)
  TestRpnParse("6i s");              (* 0 1 4 9 16 25                *)
  TestRpnParse("9i 10* 10+ 6i s +"); (* 10 21 34 49 66 85 95 105 115 *)
END RpnTest;

PROCEDURE TestPriorityParse(s: ARRAY OF CHAR);
VAR i: Int;
BEGIN
  w.s("Pri  "); w.s(s); w.nb; w.s("  ");
  i := StringLength(s);  WHILE i < 18 DO w.c(' '); INC(i) END;
  Print(PriorityParse(s)); w.l;
END TestPriorityParse;

PROCEDURE PriorityTest;
BEGIN
  TestPriorityParse("1+2-(5-1)");     (* -1                      *)
  TestPriorityParse("2*3+1");         (* 7                       *)
  TestPriorityParse("1+2*3");         (* 7                       *)
  TestPriorityParse("1+2*3+4");       (* 11                      *)
  TestPriorityParse("1+2*i4");        (* 1 3 5 7                 *)
  TestPriorityParse("1+i4*2");        (* 1 3 5 7                 *)
  TestPriorityParse("i4r3");          (* 0 1 2 3 0 1 2 3 0 1 2 3 *)
  TestPriorityParse("/+5");           (* 5                       *)
  TestPriorityParse("/+i5");          (* 10                      *)
  TestPriorityParse("/-i5");          (* -10                     *)
  TestPriorityParse("/*i5");          (* 0                       *)
  TestPriorityParse("/*(i5+1)");      (* 120                     *)
  TestPriorityParse("1 2 3 4");       (* 1 2 3 4                 *)
  TestPriorityParse("1 2 3 4 r 3");   (* 1 2 3 4 1 2 3 4 1 2 3 4 *)
  TestPriorityParse("1 2 3 4 + 10");  (* 11 12 13 14             *)
  TestPriorityParse("/+ 5 15 27");    (* 47                      *)
END PriorityTest;




(* ------------------------------------------------------------------------ *)

PROCEDURE Test*;
BEGIN
  RpnTest;
  PriorityTest
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
  Operators[ORD('r')].dyadic := Repeat;
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
