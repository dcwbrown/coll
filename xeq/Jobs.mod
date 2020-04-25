MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

CONST
Add = 0; Sub = 1; Mul = 2; Div = 3;
Neg = 4; Not = 5; Sqr = 6;

(*  All objects behave as feeds, supporting the following functions:
      Reset - reposition to first item
      More  - whether there are more items beyond the current item.
      Next  - advance to the next item, or to End if no more.
      End   - if has been advanced beyond the last item. Cur is not valid.


      Hmm, consider disallowing advance beyond last item.
      The only limitation I see is that this disallows zero item sequences.
      It simplifies by the removal of End() and of the possibility of
      no current value.
      It has a big benefit of unifying the behaviour of single items (which currently
      don't advance to End) and sequences (whch do, and with quite a lof of special
      case handling).
*)
TYPE

i8 = SYSTEM.INT8;  i16 = SYSTEM.INT16;  i32 = SYSTEM.INT32;  i64 = SYSTEM.INT64;

Ref        = POINTER TO Obj;        Obj       = RECORD next: Ref END;

anInt      = POINTER TO Int;        Int       = RECORD (Obj) i: i64                    END;
aMonadic   = POINTER TO Monadic;    Monadic   = RECORD (Obj) p: Ref; op: i64           END;
aDyadic    = POINTER TO Dyadic;     Dyadic    = RECORD (Obj) p1, p2: Ref; op: i64      END;
anIota     = POINTER TO Iota;       Iota      = RECORD (Obj) first, cur, inc, lim: i64 END;
aRepeat    = POINTER TO Repeat;     Repeat    = RECORD (Obj) p: Ref; cur, count: i64   END;
aList      = POINTER TO List;       List      = RECORD (Obj) first, cur: Ref           END;
aMatch     = POINTER TO Match;      Match     = RECORD (Obj) alt: aMatch               END;
aNonLetter = POINTER TO NonLetter;  NonLetter = RECORD (Match)                         END;
aCharMatch = POINTER TO CharMatch;  CharMatch = RECORD (Match) ch: i64                 END;

PROCEDURE (VAR o: Obj) Reset;             BEGIN                                    END Reset;
PROCEDURE (VAR o: Obj) Next;              BEGIN                                    END Next;
PROCEDURE (VAR o: Obj) More(): BOOLEAN;   BEGIN RETURN FALSE                       END More;
PROCEDURE (VAR o: Obj) Val():  i64;       BEGIN w.Fail("Abstract Obj.Val called.") END Val;

PROCEDURE (VAR i: Int) Val(): i64;        BEGIN RETURN i.i END Val;
PROCEDURE (VAR i: Int) Init(n: i64);      BEGIN i.i := n   END Init;

PROCEDURE (VAR i: Iota) Reset;            BEGIN i.cur := i.first                          END Reset;
PROCEDURE (VAR i: Iota) Next;             BEGIN IF i.More() THEN INC(i.cur, i.inc) END    END Next;
PROCEDURE (VAR i: Iota) More(): BOOLEAN;  BEGIN RETURN i.cur + i.inc < i.lim              END More;
PROCEDURE (VAR i: Iota) Val():  i64;      BEGIN w.Assert(i.cur < i.lim, ""); RETURN i.cur END Val;
PROCEDURE (VAR i: Iota) Init(f,n,l: i64); BEGIN i.first:=f; i.inc:=n; i.lim:=l; i.Reset   END Init;

PROCEDURE (VAR r: Repeat) Reset;                BEGIN r.p.Reset;  r.cur := 0                   END Reset;
PROCEDURE (VAR r: Repeat) More(): BOOLEAN;      BEGIN RETURN (r.cur+1 < r.count) OR r.p.More() END More;
PROCEDURE (VAR r: Repeat) Val():  i64;          BEGIN RETURN r.p.Val()                         END Val;
PROCEDURE (VAR r: Repeat) Init(p: Ref; c: i64); BEGIN  r.p := p;  r.count := c;  r.Reset       END Init;
PROCEDURE (VAR r: Repeat) Next;
BEGIN IF r.More() THEN
  IF r.p.More() THEN  r.p.Next  ELSE  r.p.Reset; INC(r.cur)  END
END END Next;


PROCEDURE (VAR l: List) Reset;            BEGIN l.cur := l.first                            END Reset;
PROCEDURE (VAR l: List) More(): BOOLEAN;  BEGIN RETURN l.cur.next # NIL                     END More;
PROCEDURE (VAR l: List) Next;             BEGIN IF l.More() THEN l.cur := l.cur.next END END Next;
PROCEDURE (VAR l: List) Val():  i64;      BEGIN RETURN l.cur(anInt).i                       END Val;
PROCEDURE (VAR l: List) Init(i: Ref);     BEGIN l.first := i; l.Reset                       END Init;

PROCEDURE (VAR m: Monadic) Reset;           BEGIN m.p.Reset            END Reset;
PROCEDURE (VAR m: Monadic) Next;            BEGIN m.p.Next             END Next;
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

PROCEDURE (VAR d: Dyadic) Reset;           BEGIN d.p1.Reset; d.p2.Reset            END Reset;
PROCEDURE (VAR d: Dyadic) Next;            BEGIN d.p1.Next; d.p2.Next              END Next;
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


PROCEDURE (VAR m: Match) Matches(c: i64): BOOLEAN; BEGIN w.Fail("Abstract Match.Matches() called.") END Matches;

PROCEDURE (VAR l: List) IsMatch(): BOOLEAN;       BEGIN RETURN l.cur IS aMatch           END IsMatch;
PROCEDURE (VAR l: List) HasAlt():  BOOLEAN;       BEGIN RETURN l.cur(aMatch).alt # NIL   END HasAlt;
PROCEDURE (VAR l: List) Alt;                      BEGIN l.cur := l.cur(aMatch).alt       END Alt;
PROCEDURE (VAR l: List) Matches(c: i64): BOOLEAN; BEGIN RETURN l.cur(aMatch).Matches(c)  END Matches;

PROCEDURE (VAR m: CharMatch) Matches(c: i64): BOOLEAN;
BEGIN RETURN c = m.ch END Matches;

PROCEDURE (VAR m: NonLetter) Matches(c: i64): BOOLEAN;
BEGIN RETURN  (c < ORD('A'))
          OR  (c > ORD('z'))
          OR ((c > ORD('Z')) & (c < ORD('a'))) END Matches;

PROCEDURE Print(r: Ref);
BEGIN  r.Reset;  w.i(r.Val());  WHILE r.More() DO r.Next; w.i(r.Val()) END
END Print;

PROCEDURE Lookup(s: ARRAY [1] OF CHAR; beg, end: i64; n: aMatch);
VAR i: i64; l: List;
BEGIN
  i := beg;  l.Init(n);
  LOOP
    IF i >= end THEN w.sl("Lookup reached end of string."); EXIT END;
    IF l.IsMatch() THEN
      IF l.Matches(ORD(s[i])) THEN
        IF l.More() THEN
          INC(i); l.Next
        ELSE
          w.sl("Lookup matched character but no more in sequence."); EXIT
        END
      ELSE
        IF l.HasAlt() THEN
          l.Alt
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

PROCEDURE Test*;
VAR
  i1, i2:   anInt;
  a:        aDyadic;
  io1, io2: anIota;
  m:        aMonadic;
  r:        aRepeat;
BEGIN  NEW(i1);  NEW(i2);  NEW(a);  NEW(io1);  NEW(io2);  NEW(m);  NEW(r);
  i1.Init(10);                           Print(i1);   w.l; (* 10                           *)
  i2.Init(2);                            Print(i2);   w.l; (* 2                            *)
  a.Init(i1, i2, Add);                   Print(a);    w.l; (* 12                           *)
  io1.Init(0, 1, 5);                     Print(io1);  w.l; (* 0 1 2 3 4                    *)
                                         Print(io1);  w.l; (* 0 1 2 3 4                    *)
  r.Init(io1, 2);                        Print(r);    w.l; (* 0 1 2 3 4 0 1 2 3 4          *)
  r.Init(i1, 8);  a.Init(r, io1, Add);   Print(a);    w.l; (* 10 11 12 13 14 14 14 14      *)
  io1.Init(0, 1, 6);                     Print(io1);  w.l; (* 0 1 2 3 4 5                  *)
  io2.Init(10, 10, 100);                 Print(io2);  w.l; (* 10 20 30 40 50 60 70 80 90   *)
  a.Init(io1, io2, Add);                 Print(a);    w.l; (* 10 21 32 43 54 65 75 85 95   *)
  m.Init(io1, Sqr);                      Print(m);    w.l; (* 0 1 4 9 16 25                *)
  a.Init(m, io2, Add);                   Print(a);    w.l; (* 10 21 34 49 66 85 95 105 115 *)

  TestMatch
END Test;

END Jobs.
