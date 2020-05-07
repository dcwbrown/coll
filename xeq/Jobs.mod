MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

CONST
  (* Object kinds *)
  Nobj     = 0;                  (* None                            *)
  Integer  = 1;                  (* a singleton integer value       *)
  Iota     = 2;                  (* a vector of 0 up to a limit     *)
  Repeat   = 3;                  (* repeats a source multiple times *)
  Negate   = 4;   Invert   = 5;  (* monadic operators               *)
  Square   = 6;                  (* monadic operators               *)
  Add      = 7;   Subtract = 8;  (* dyadic operators                *)
  Multiply = 9;   Divide   = 10; (* dyadic operators                *)
  ObjLimit = 11;

  (* Special integer value placeholder for lazy evaluation *)
  Pending = MIN(SYSTEM.INT64);

TYPE
  Int = SYSTEM.INT64;
  Ref = POINTER TO Obj;
  Obj = RECORD  kind: Int;  left, right: Ref;  current, last: Int  END;

PROCEDURE Reset(r: Ref);
BEGIN IF r # NIL THEN r.current := 0;  Reset(r.left);  Reset(r.right) END
END Reset;

PROCEDURE Value(r: Ref): Int;
BEGIN CASE r.kind OF
|Integer:  RETURN r.last
|Repeat:   RETURN Value(r.left)
|Iota:     RETURN r.current
|Negate:   RETURN -Value(r.left)
|Invert:   RETURN -Value(r.left) - 1
|Square:   RETURN Value(r.left)  *  Value(r.left)
|Add:      RETURN Value(r.left)  +  Value(r.right)
|Subtract: RETURN Value(r.left)  -  Value(r.right)
|Multiply: RETURN Value(r.left)  *  Value(r.right)
|Divide:   RETURN Value(r.left) DIV Value(r.right)
ELSE
END END Value;

PROCEDURE More(r: Ref): BOOLEAN;
BEGIN
  IF r # NIL THEN
    IF r.last = Pending THEN r.last := Value(r.right)-1; r.right := NIL END;
    CASE r.kind OF
    |Negate, Invert, Square, Add, Subtract, Multiply, Divide:
             RETURN More(r.left) OR More(r.right)
    |Iota:   RETURN r.current < r.last
    |Repeat: RETURN (r.current < r.last) OR More(r.left)
    ELSE
    END
  END;
RETURN FALSE END More;

PROCEDURE Advance(r: Ref);
BEGIN
  w.Assert(r.last # Pending, "Advance called with r.last unexpectedly pending, More() should have been called first.");
  CASE r.kind OF
  |Negate, Invert, Square, Add, Subtract, Multiply, Divide:
           IF More(r.left)  THEN Advance(r.left)  END;
           IF More(r.right) THEN Advance(r.right) END
  |Iota:   IF r.current < r.last THEN INC(r.current) END
  |Repeat: IF More(r.left) THEN
             Advance(r.left)
           ELSIF r.current < r.last THEN
             Reset(r.left);  INC(r.current)
           END
  ELSE
  END
END Advance;

PROCEDURE Print(r: Ref);
BEGIN  Reset(r);  w.i(Value(r));
  WHILE More(r) DO Advance(r); w.i(Value(r)) END
END Print;

PROCEDURE MakeObj(kind: Int; left, right: Ref; last: Int): Ref;
VAR r: Ref;
BEGIN NEW(r);
  r.kind := kind;
  r.left := left;  r.right := right;
  r.current := 0;  r.last  := last;
RETURN r; END MakeObj;

PROCEDURE RpnParse(s: ARRAY OF CHAR): Ref;
VAR r: Ref;  acc, i, top: Int;  stk: ARRAY 3 OF Ref;
  PROCEDURE Push(r: Ref); BEGIN INC(top); stk[top] := r     END Push;
  PROCEDURE Pop(): Ref;   BEGIN DEC(top); RETURN stk[top+1] END Pop;
BEGIN i := 0;  top := -1;
  WHILE i < LEN(s) DO
    IF (s[i] >= '0') & (s[i] <= '9') THEN
      acc := ORD(s[i]) - ORD('0'); INC(i);
      WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
        acc := acc*10 + ORD(s[i]) - ORD('0');  INC(i)
      END;
      NEW(r);  r.kind := Integer;  r.current := 0;  r.last := acc;  Push(r);
    ELSE
      CASE s[i] OF
      |'n': Push(MakeObj(Negate,   Pop(), NIL,   0))
      |'~': Push(MakeObj(Invert,   Pop(), NIL,   0))
      |'s': Push(MakeObj(Square,   Pop(), NIL,   0))
      |'+': Push(MakeObj(Add,      Pop(), Pop(), 0))
      |'-': Push(MakeObj(Subtract, Pop(), Pop(), 0))
      |'*': Push(MakeObj(Multiply, Pop(), Pop(), 0))
      |'/': Push(MakeObj(Divide,   Pop(), Pop(), 0))
      |'#': Push(MakeObj(Repeat,   Pop(), Pop(), Pending))
      |'i': Push(MakeObj(Iota,     NIL,   Pop(), Pending))
      |' ', 00X:
      ELSE  w.s("Unexpected character '"); w.c(s[i]); w.s("' in RpnParse input."); w.Fail('');
      END;
      INC(i)
    END
  END;
  w.Assert(top = 0, "Stack does not have single entry at RpnParse completion.");
  RETURN stk[top]
END RpnParse;

PROCEDURE Test*;
VAR r: Ref;
BEGIN
  Print(RpnParse("10")); w.l;                (* 10                           *)
  Print(RpnParse("2")); w.l;                 (* 2                            *)
  Print(RpnParse("10 2 +")); w.l;            (* 12                           *)
  r := RpnParse("5i");  Print(r); w.l;       (* 0 1 2 3 4                    *)
  Print(r); w.l;                             (* 0 1 2 3 4                    *)
  Print(RpnParse("1 2 #")); w.l;             (* 1 1                          *)
  Print(RpnParse("5i 2#")); w.l;             (* 0 1 2 3 4 0 1 2 3 4          *)
  Print(RpnParse("10 8# 5i +")); w.l;        (* 10 11 12 13 14 14 14 14      *)
  Print(RpnParse("9i 10*")); w.l;            (* 0 10 20 30 40 50 60 70 80    *)
  Print(RpnParse("9i 10* 10+")); w.l;        (* 10 20 30 40 50 60 70 80 90   *)
  Print(RpnParse("6i 9i 10* 10+ +")); w.l;   (* 10 21 32 43 54 65 75 85 95   *)
  Print(RpnParse("6i s")); w.l;              (* 0 1 4 9 16 25                *)
  Print(RpnParse("9i 10* 10+ 6i s +")); w.l; (* 10 21 34 49 66 85 95 105 115 *)
END Test;

END Jobs.


------------------------------------------------------------------------------

  (* Operations *)
  Non = 0;
  (* Monadic *)
  Idn = 1; Neg = 2; Not = 3; Sqr = 4; Iot = 5;
  (* Dyadic *)
  Add = 6; Sub = 7; Mul = 8; Div = 9; Rep = 10;
  OpLimit = 11;

aMatch     = POINTER TO Match;      Match     = RECORD (Obj) next, alt: aMatch       END;
aNonLetter = POINTER TO NonLetter;  NonLetter = RECORD (Match)                       END;
aCharMatch = POINTER TO CharMatch;  CharMatch = RECORD (Match) ch: Int               END;
aPattern   = POINTER TO Pattern;    Pattern   = RECORD (Obj) first, cur: Ref         END;

VAR OpLevel: ARRAY OpLimit OF Int;


(*
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

*)

PROCEDURE PriorityParse(s: ARRAY OF CHAR): Ref;
VAR i: Int;

  PROCEDURE ts;  (* Trace string *)
  VAR j: Int;
  BEGIN j := i;
    w.s('"');
    WHILE (j < LEN(s)) & (s[j] # 0X) DO w.c(s[j]); INC(j) END;
    w.s('"')
  END ts;

  PROCEDURE skipSpace;
  BEGIN
    WHILE (i < LEN(s)) & (s[i] <= ' ') DO INC(i) END
  END skipSpace;

  PROCEDURE expect(c: CHAR);
  BEGIN skipSpace;
    w.Assert((i < LEN(s)) & (s[i] = c), "Unexpected character in PriorityParse");
    INC(i)
  END expect;

  PROCEDURE^ ParseDyadic(priority: Int): Ref;

  PROCEDURE ParseIntegerLiteral(): Ref;
  VAR  acc: Int;  Int: anInt;
  BEGIN  acc := 0;
    WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
      acc := acc*10 + ORD(s[i]) - ORD('0');
      INC(i);
    END;
    NEW(Int);  Int.i := acc;
  RETURN Int END ParseIntegerLiteral;

  PROCEDURE ParseOperand(): Ref;
  VAR  result: Ref;
  BEGIN
    skipSpace;  w.Assert(i < LEN(s), "Nothing left for ParseOperand.");
    IF s[i] = '(' THEN
      INC(i);
      result := ParseDyadic(0);
      expect(')')
    ELSIF (s[i] >= '0') & (s[i] <= '9') THEN
      result := ParseIntegerLiteral();
    ELSE
      w.Fail("Nothing suitable for ParseOperand.");
    END;
  RETURN result END ParseOperand;

  PROCEDURE ParseMonadic(): Ref;
  VAR  result: Ref;  op: Int;  mon: aMonadic;  iot: anIota;
  BEGIN  op := Non;
    skipSpace;
    IF Trace THEN w.s("ParseMonadic "); ts; w.sl(".") END;
    IF i < LEN(s) THEN
      CASE s[i] OF
      |"+": op := Idn
      |"-": op := Neg
      |"i": op := Iot
      ELSE
      END
    END;
    IF op = Non THEN
      result := ParseOperand()
    ELSE
      INC(i);
      CASE op OF
      |Idn: result := ParseMonadic()
      |Neg: NEW(mon);  mon.Init(ParseMonadic(), Neg);  result := mon
      |Iot: NEW(iot);  iot.Init(ParseMonadic());       result := iot
      ELSE  result := ParseOperand()
      END
    END;
  RETURN result END ParseMonadic;

  (*  ParseDyadicOperator
      Skips spaces

      If the next character is               Returns
      ------------------------               -------
      not an operator                        Non, doesn't advance.
      an operator at a lower priority        Non, doesn't advance
      an operator at >= requested priority   The operation, does advance
  *)
  PROCEDURE ParseDyadicOperator(priority: Int): Int;
  VAR result: Int;
  BEGIN
    IF Trace THEN w.s("  ParseDyadicOperator <"); w.i(priority); w.s(">: "); ts; END;
    result := Non;
    skipSpace;
    IF i < LEN(s) THEN
      CASE s[i] OF
      |'+': result := Add
      |'-': result := Sub
      |'*': result := Mul
      |'/': result := Div
      |'r': result := Rep
      ELSE
      END;
      IF result # Non THEN
        IF    OpLevel[result] < priority THEN
          result := Non
        ELSE
          INC(i)
        END
      END
    END;
    IF Trace THEN
      w.s(", result: ");
      CASE result OF
      |Non: w.s("Non")
      |Add: w.s("Add")
      |Sub: w.s("Sub")
      |Mul: w.s("Mul")
      |Div: w.s("Div")
      |Rep: w.s("Rep")
      ELSE w.i(result)
      END;
      w.sl(".")
    END;
  RETURN result END ParseDyadicOperator;

  PROCEDURE MakeDyadic(left, right: Ref; op: Int): Ref;
  VAR  dya: aDyadic;  rep: aRepeat;  result: Ref;
  BEGIN
    CASE op OF
    |Add, Sub, Mul, Div:
      NEW(dya);  dya.Init(left, right, op);  result := dya
    |Rep:
      NEW(rep);  rep.Init(left, Value(right));  result := rep
    ELSE w.Fail("Unexpected op passed to MakeDyadic")
    END;
  RETURN result END MakeDyadic;

  PROCEDURE ParseDyadic(priority: Int): Ref;
  VAR  op: Int;  left, right: Ref;  dya: aDyadic;
  BEGIN
    IF Trace THEN w.s("ParseDyadic <"); w.i(priority); w.s(">: "); ts; w.sl(".") END;
    left := ParseMonadic();
    op := ParseDyadicOperator(priority);
    WHILE op # Non DO
      right := ParseDyadic(OpLevel[op]+1);
      left := MakeDyadic(left, right, op);
      op := ParseDyadicOperator(priority)
    END;
    IF Trace THEN w.s("ParseDyadic complete, leaving"); ts; w.sl(".") END;
  RETURN left END ParseDyadic;

BEGIN i := 0;
  IF Trace THEN w.s('PriorityParse("'); w.s(s); w.sl('").') END;
  RETURN ParseDyadic(0)
END PriorityParse;

PROCEDURE StringLength(s: ARRAY [1] OF CHAR): Int;
VAR i: Int;
BEGIN i := 0;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO INC(i) END;
RETURN i END StringLength;

PROCEDURE TestPriorityParse(s: ARRAY OF CHAR);
VAR i: Int;
BEGIN
  w.s("  "); w.s(s); w.nb; w.s(": ");
  i := StringLength(s);
  WHILE i < 15 DO w.c(' '); INC(i) END;
  Print(PriorityParse(s)); w.l;
END TestPriorityParse;

PROCEDURE Test*;
BEGIN
  TestMatch;

  TestPriorityParse("1+2-(5-1)");
  TestPriorityParse("2*3+1");
  TestPriorityParse("1+2*3");
  TestPriorityParse("1+2*3+4");
  TestPriorityParse("1+2*i4");
  TestPriorityParse("1+i4*2");
  TestPriorityParse("i4r3");
END Test;

BEGIN
  OpLevel[0]  := 0;  (*  *)
  OpLevel[1]  := 0;  (* Idn *)
  OpLevel[2]  := 0;  (* Neg *)
  OpLevel[3]  := 0;  (* Not *)
  OpLevel[4]  := 0;  (* Sqr *)
  OpLevel[5]  := 0;  (* Iot *)
  OpLevel[6]  := 0;  (* Add *)
  OpLevel[7]  := 0;  (* Sub *)
  OpLevel[8]  := 1;  (* Mul *)
  OpLevel[9]  := 1;  (* Div *)
  OpLevel[10] := 2;  (* Rep *)
END Jobs.