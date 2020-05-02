MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

CONST
Add = 0; Sub = 1; Mul = 2; Div = 3;
Neg = 4; Not = 5; Sqr = 6;

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
aString    = POINTER TO String;     String    = RECORD (Obj) l: i64; s: Str          END;
aMatch     = POINTER TO Match;      Match     = RECORD (Obj) next, alt: aMatch       END;
aNonLetter = POINTER TO NonLetter;  NonLetter = RECORD (Match)                       END;
aCharMatch = POINTER TO CharMatch;  CharMatch = RECORD (Match) ch: i64               END;
aPattern   = POINTER TO Pattern;    Pattern   = RECORD (Obj) first, cur: Ref         END;

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
PROCEDURE (VAR i: Iota) Init(l: i64);     BEGIN i.lim:=l;  i.Reset              END Init;

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
      |'i': NEW(iot); iot.Init(stk[top].Val());  stk[top] := iot
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

END Test;

END Jobs.
