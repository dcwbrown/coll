MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

CONST
  Trace = FALSE;

  (* Operations *)
  Non = 0;
  (* Monadic *)
  Idn = 1; Neg = 2; Not = 3; Sqr = 4; Iot = 5;
  (* Dyadic *)
  Add = 6; Sub = 7; Mul = 8; Div = 9; Rep = 10;
  OpLimit = 11;

(*  All objects behave as feeds, supporting the following functions:
      Reset   - reposition to first item
      More    - whether there are more items beyond the current item.
      Advance - advance to the Advance item, or to End if no more.
*)
TYPE

i8 = SYSTEM.INT8;  i16 = SYSTEM.INT16;  i32 = SYSTEM.INT32;  i64 = SYSTEM.INT64;

Str = POINTER TO ARRAY OF CHAR;

Ref        = POINTER TO Obj;        Obj       = RECORD END;

anInt      = POINTER TO Int;        Int       = RECORD (Obj) i: i64                  END;
aMonadic   = POINTER TO Monadic;    Monadic   = RECORD (Obj) p: Ref; op: i64         END;
aDyadic    = POINTER TO Dyadic;     Dyadic    = RECORD (Obj) p1, p2: Ref; op: i64    END;
anIota     = POINTER TO Iota;       Iota      = RECORD (Obj) cur, lim: i64           END;
aRepeat    = POINTER TO Repeat;     Repeat    = RECORD (Obj) p: Ref; cur, count: i64 END;
aString    = POINTER TO String;     String    = RECORD (Obj) cur: i64; s: Str        END;
aMatch     = POINTER TO Match;      Match     = RECORD (Obj) next, alt: aMatch       END;
aNonLetter = POINTER TO NonLetter;  NonLetter = RECORD (Match)                       END;
aCharMatch = POINTER TO CharMatch;  CharMatch = RECORD (Match) ch: i64               END;
aPattern   = POINTER TO Pattern;    Pattern   = RECORD (Obj) first, cur: Ref         END;

VAR OpLevel: ARRAY OpLimit OF i64;

PROCEDURE (VAR o: Obj) Reset;             BEGIN                                    END Reset;
PROCEDURE (VAR o: Obj) Advance;           BEGIN                                    END Advance;
PROCEDURE (VAR o: Obj) More(): BOOLEAN;   BEGIN RETURN FALSE                       END More;
PROCEDURE (VAR o: Obj) Val():  i64;       BEGIN w.Fail("Abstract Obj.Val called.") END Val;

PROCEDURE (VAR i: Int) Val(): i64;        BEGIN RETURN i.i END Val;
PROCEDURE (VAR i: Int) Init(n: i64);      BEGIN i.i := n   END Init;

PROCEDURE (VAR i: Iota) Reset;            BEGIN i.cur := 0                      END Reset;
PROCEDURE (VAR i: Iota) Advance;          BEGIN IF i.More() THEN INC(i.cur) END END Advance;
PROCEDURE (VAR i: Iota) More(): BOOLEAN;  BEGIN RETURN i.cur+1 < i.lim          END More;
PROCEDURE (VAR i: Iota) Val():  i64;      BEGIN RETURN i.cur                    END Val;
PROCEDURE (VAR i: Iota) Init(l: Ref);     BEGIN i.lim := l.Val();  i.Reset      END Init;

PROCEDURE (VAR r: Repeat) Reset;                BEGIN r.p.Reset;  r.cur := 0                   END Reset;
PROCEDURE (VAR r: Repeat) More(): BOOLEAN;      BEGIN RETURN (r.cur+1 < r.count) OR r.p.More() END More;
PROCEDURE (VAR r: Repeat) Val():  i64;          BEGIN RETURN r.p.Val()                         END Val;
PROCEDURE (VAR r: Repeat) Init(p: Ref; c: i64); BEGIN  r.p := p;  r.count := c;  r.Reset       END Init;
PROCEDURE (VAR r: Repeat) Advance;
BEGIN IF r.More() THEN
  IF r.p.More() THEN  r.p.Advance  ELSE  r.p.Reset; INC(r.cur)  END
END END Advance;

PROCEDURE (VAR m: Monadic) Reset;           BEGIN m.p.Reset            END Reset;
PROCEDURE (VAR m: Monadic) Advance;         BEGIN m.p.Advance          END Advance;
PROCEDURE (VAR m: Monadic) More(): BOOLEAN; BEGIN RETURN m.p.More()    END More;
PROCEDURE (VAR m: Monadic) Val():  i64;
VAR  i: i64;
BEGIN i := m.p.Val();
  CASE m.op OF Neg: RETURN -i | Not: RETURN -i-1 | Sqr: RETURN i*i
  ELSE w.Fail("Unknown monadic operation.")
  END
END Val;
PROCEDURE (VAR m: Monadic) Init(p: Ref; op: i64);
BEGIN  m.p := p;  m.op := op  END Init;

PROCEDURE (VAR d: Dyadic) Reset;           BEGIN d.p1.Reset;   d.p2.Reset          END Reset;
PROCEDURE (VAR d: Dyadic) Advance;         BEGIN d.p1.Advance; d.p2.Advance        END Advance;
PROCEDURE (VAR d: Dyadic) More(): BOOLEAN; BEGIN RETURN d.p1.More() OR d.p2.More() END More;
PROCEDURE (VAR d: Dyadic) Val():  i64;
VAR  i1, i2: i64;
BEGIN  i1 := d.p1.Val();  i2 := d.p2.Val();
  CASE d.op OF Add: RETURN i1+i2 | Sub: RETURN i1-i2 | Mul: RETURN i1*i2 | Div: RETURN i1 DIV i2
  ELSE w.Fail("Unknown dyadic operation.")
  END
END Val;
PROCEDURE (VAR d: Dyadic) Init(p1, p2: Ref; op: i64);
BEGIN  d.p1 := p1;  d.p2 := p2;  d.op := op  END Init;

PROCEDURE (VAR m: Match)     Matches(c: i64): BOOLEAN; BEGIN w.Fail("Abstract Match.Matches() called.") END Matches;
PROCEDURE (VAR m: CharMatch) Matches(c: i64): BOOLEAN; BEGIN RETURN c = m.ch                END Matches;
PROCEDURE (VAR m: NonLetter) Matches(c: i64): BOOLEAN;
BEGIN RETURN  (c < ORD('A'))
          OR  (c > ORD('z'))
          OR ((c > ORD('Z')) & (c < ORD('a'))) END Matches;

PROCEDURE (VAR p: Pattern) Reset;            BEGIN p.cur := p.first                         END Reset;
PROCEDURE (VAR p: Pattern) Val():  i64;      BEGIN RETURN p.cur(aCharMatch).ch              END Val;
PROCEDURE (VAR p: Pattern) Init(m: aMatch);  BEGIN p.first := m; p.Reset                    END Init;
PROCEDURE (VAR p: Pattern) IsMatch(): BOOLEAN;       BEGIN RETURN p.cur IS aMatch           END IsMatch;
PROCEDURE (VAR p: Pattern) Matches(c: i64): BOOLEAN; BEGIN RETURN p.cur(aMatch).Matches(c)  END Matches;

PROCEDURE (VAR p: Pattern) More(): BOOLEAN;
BEGIN RETURN (p.cur IS aMatch) & (p.cur(aMatch).next # NIL) END More;

PROCEDURE (VAR p: Pattern) Advance;
BEGIN IF p.More() THEN p.cur := p.cur(aMatch).next END END Advance;

PROCEDURE (VAR p: Pattern) HasAlt(): BOOLEAN;
BEGIN RETURN (p.cur IS aMatch) & (p.cur(aMatch).alt # NIL) END HasAlt;

PROCEDURE (VAR p: Pattern) Alt;
BEGIN p.cur := p.cur(aMatch).alt END Alt;


PROCEDURE Print(r: Ref);
BEGIN  r.Reset;  w.i(r.Val());  WHILE r.More() DO r.Advance; w.i(r.Val()) END
END Print;

PROCEDURE Lookup(s: ARRAY [1] OF CHAR; beg, end: i64; n: aMatch);
VAR i: i64; p: Pattern;
BEGIN
  i := beg;  p.Init(n);
  LOOP
    IF i >= end THEN w.sl("Lookup reached end of string."); EXIT END;
    IF p.IsMatch() THEN
      IF p.Matches(ORD(s[i])) THEN
        IF p.More() THEN
          INC(i); p.Advance
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
  NEW(cn); cn.ch := ORD('O');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('D');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('U');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('L');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('E');  n.next := cn;  n := cn;
  NEW(nl);                     n.next := nl;  n := nl;

  Lookup("MODULE fred;", 0, 12, r);
  Lookup("MUDDY", 0, 5, r);
  Lookup("MOD", 0, 3, r);

END TestMatch;

PROCEDURE RpnParse(s: ARRAY OF CHAR): Ref;
VAR
  i:   i64;
  int: anInt;
  mon: aMonadic;
  dya: aDyadic;
  iot: anIota;
  rep: aRepeat;
  stk: ARRAY 3 OF Ref;
  top: INTEGER;
  acc: i64;

BEGIN i := 0;  top := -1;
  WHILE i < LEN(s) DO
    (* w.s("('"); w.c(s[i]); w.sl("')"); *)
    IF (s[i] >= '0') & (s[i] <= '9') THEN
      NEW(int);
      int.i := ORD(s[i]) - ORD('0'); INC(i);
      WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
        int.i := int.i*10 + ORD(s[i]) - ORD('0');
        INC(i)
      END;
      INC(top); stk[top] := int;
    ELSE
      CASE s[i] OF
      |'n': NEW(mon); mon.Init(stk[top], Neg);                        stk[top] := mon
      |'~': NEW(mon); mon.Init(stk[top], Not);                        stk[top] := mon
      |'s': NEW(mon); mon.Init(stk[top], Sqr);                        stk[top] := mon
      |'+': NEW(dya); dya.Init(stk[top-1], stk[top], Add);  DEC(top); stk[top] := dya
      |'-': NEW(dya); dya.Init(stk[top-1], stk[top], Sub);  DEC(top); stk[top] := dya
      |'*': NEW(dya); dya.Init(stk[top-1], stk[top], Mul);  DEC(top); stk[top] := dya
      |'/': NEW(dya); dya.Init(stk[top-1], stk[top], Div);  DEC(top); stk[top] := dya
      |'#': NEW(rep); rep.Init(stk[top-1], stk[top].Val()); DEC(top); stk[top] := rep
      |'i': NEW(iot); iot.Init(stk[top]);                             stk[top] := iot
      |00X: (* w.sl("(zero)"); *)
      |' ': (* w.sl("(space)"); *)
      ELSE  w.s("Unexpected character '"); w.c(s[i]); w.s("' in RpnParse input."); w.Fail('');
      END;
      INC(i)
    END
  END;
  w.Assert(top = 0, "Stack does not have single entry at RpnParse completion.");
  RETURN stk[top]
END RpnParse;


PROCEDURE PriorityParse(s: ARRAY OF CHAR): Ref;
VAR i: i64;

  PROCEDURE ts;  (* Trace string *)
  VAR j: i64;
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

  PROCEDURE^ ParseDyadic(priority: i64): Ref;

  PROCEDURE ParseIntegerLiteral(): Ref;
  VAR  acc: i64;  int: anInt;
  BEGIN  acc := 0;
    WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
      acc := acc*10 + ORD(s[i]) - ORD('0');
      INC(i);
    END;
    NEW(int);  int.i := acc;
  RETURN int END ParseIntegerLiteral;

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
  VAR  result: Ref;  op: i64;  mon: aMonadic;  iot: anIota;
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
  PROCEDURE ParseDyadicOperator(priority: i64): i64;
  VAR result: i64;
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

  PROCEDURE MakeDyadic(left, right: Ref; op: i64): Ref;
  VAR  dya: aDyadic;  rep: aRepeat;  result: Ref;
  BEGIN
    CASE op OF
    |Add, Sub, Mul, Div:
      NEW(dya);  dya.Init(left, right, op);  result := dya
    |Rep:
      NEW(rep);  rep.Init(left, right.Val());  result := rep
    ELSE w.Fail("Unexpected op passed to MakeDyadic")
    END;
  RETURN result END MakeDyadic;

  PROCEDURE ParseDyadic(priority: i64): Ref;
  VAR  op: i64;  left, right: Ref;  dya: aDyadic;
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

PROCEDURE StringLength(s: ARRAY [1] OF CHAR): i64;
VAR i: i64;
BEGIN i := 0;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO INC(i) END;
RETURN i END StringLength;

PROCEDURE TestPriorityParse(s: ARRAY OF CHAR);
VAR i: i64;
BEGIN
  w.s("  "); w.s(s); w.nb; w.s(": ");
  i := StringLength(s);
  WHILE i < 15 DO w.c(' '); INC(i) END;
  Print(PriorityParse(s)); w.l;
END TestPriorityParse;

PROCEDURE Test*;
VAR o: Ref;
BEGIN
  Print(RpnParse("10")); w.l;                (* 10                           *)
  Print(RpnParse("2")); w.l;                 (* 2                            *)
  Print(RpnParse("10 2 +")); w.l;            (* 12                           *)
  o := RpnParse("5i");  Print(o); w.l;       (* 0 1 2 3 4                    *)
  Print(o); w.l;                             (* 0 1 2 3 4                    *)
  Print(RpnParse("5i 2#")); w.l;             (* 0 1 2 3 4 0 1 2 3 4          *)
  Print(RpnParse("10 8# 5i +")); w.l;        (* 10 11 12 13 14 14 14 14      *)
  Print(RpnParse("9i 10*")); w.l;            (* 0 10 20 30 40 50 60 70 80    *)
  Print(RpnParse("9i 10* 10+")); w.l;        (* 10 20 30 40 50 60 70 80 90   *)
  Print(RpnParse("6i 9i 10* 10+ +")); w.l;   (* 10 21 32 43 54 65 75 85 95   *)
  Print(RpnParse("6i s")); w.l;              (* 0 1 4 9 16 25                *)
  Print(RpnParse("9i 10* 10+ 6i s +")); w.l; (* 10 21 34 49 66 85 95 105 115 *)

  TestMatch;

  TestPriorityParse("1+2-(5-1)");
  TestPriorityParse("1+2*3");
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