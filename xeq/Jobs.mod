MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

CONST

Add = 0; Sub = 1; Mul = 2; Div = 3;
Neg = 4; Not = 5; Sqr = 6;


TYPE

i8 = SYSTEM.INT8;  i16 = SYSTEM.INT16;  i32 = SYSTEM.INT32;  i64 = SYSTEM.INT64;

Ref = POINTER TO Obj;  Obj = RECORD END;

Int     = RECORD (Obj) i: i64                    END;
Monadic = RECORD (Obj) p: Ref; op: i64           END;
Dyadic  = RECORD (Obj) p1, p2: Ref; op: i64      END;
Iota    = RECORD (Obj) first, cur, inc, lim: i64 END;

PROCEDURE (VAR n: Obj) Val(): i64;       BEGIN w.Fail("Abstract Obj.Val called.") END Val;
PROCEDURE (VAR n: Obj) More(): BOOLEAN;  BEGIN RETURN FALSE                       END More;
PROCEDURE (VAR n: Obj) Next;             BEGIN                                    END Next;
PROCEDURE (VAR n: Obj) Reset;            BEGIN                                    END Reset;

PROCEDURE (VAR i: Int) Val(): i64;       BEGIN RETURN i.i                         END Val;

PROCEDURE (VAR m: Monadic) More(): BOOLEAN; BEGIN RETURN m.p.More() END More;
PROCEDURE (VAR m: Monadic) Next;            BEGIN m.p.Next          END Next;
PROCEDURE (VAR m: Monadic) Reset;           BEGIN m.p.Reset         END Reset;
PROCEDURE (VAR m: Monadic) Val(): i64;
VAR  i: i64;
BEGIN i := m.p.Val();
  CASE m.op OF Neg: RETURN -i | Not: RETURN -i-1 | Sqr: RETURN i*i
  ELSE w.Fail("Unknown monadic operation.")
  END
END Val;

PROCEDURE (VAR d: Dyadic) More(): BOOLEAN; BEGIN RETURN d.p1.More() OR d.p2.More() END More;
PROCEDURE (VAR d: Dyadic) Next;            BEGIN d.p1.Next; d.p2.Next              END Next;
PROCEDURE (VAR d: Dyadic) Reset;           BEGIN d.p1.Reset; d.p2.Reset            END Reset;
PROCEDURE (VAR d: Dyadic) Val(): i64;
VAR  i1, i2: i64;
BEGIN  i1 := d.p1.Val();  i2 := d.p2.Val();
  CASE d.op OF Add: RETURN i1+i2 | Sub: RETURN i1-i2 | Mul: RETURN i1*i2 | Div: RETURN i1 DIV i2
  ELSE w.Fail("Unknown dyadic operation.")
  END
END Val;

PROCEDURE (VAR i: Iota) More(): BOOLEAN; BEGIN RETURN i.cur + i.inc < i.lim           END More;
PROCEDURE (VAR i: Iota) Next;            BEGIN IF i.More() THEN INC(i.cur, i.inc) END END Next;
PROCEDURE (VAR i: Iota) Reset;           BEGIN i.cur := i.first                       END Reset;
PROCEDURE (VAR i: Iota) Val(): i64;      BEGIN RETURN i.cur                           END Val;

PROCEDURE Print(r: Ref);
BEGIN  r.Reset;  w.i(r.Val());  WHILE r.More() DO r.Next; w.i(r.Val()) END
END Print;

PROCEDURE Test*;
VAR
  i1, i2:   POINTER TO Int;
  a:        POINTER TO Dyadic;
  io1, io2: POINTER TO Iota;
  s:        POINTER TO Monadic;
BEGIN  NEW(i1);  NEW(i2);  NEW(a);  NEW(io1);  NEW(io2);  NEW(s);
  i1.i := 1;                                          Print(i1);   w.l; (* 1                            *)
  i2.i := 2;                                          Print(i2);   w.l; (* 2                            *)
  a.op := Add;  a.p1 := i1;  a.p2 := i2;              Print(a);    w.l; (* 3                            *)
  io1.first := 0;  io1.inc := 1;  io1.lim := 5;       Print(io1);  w.l; (* 0 1 2 3 4                    *)
                                                      Print(io1);  w.l; (* 0 1 2 3 4                    *)
  i1.i := 10;  a.p2 := io1;                           Print(a);    w.l; (* 10 11 12 13 14               *)
  io1.first := 0;   io1.inc := 1;   io1.lim := 6;     Print(io1);  w.l; (* 0 1 2 3 4 5                  *)
  io2.first := 10;  io2.inc := 10;  io2.lim := 100;   Print(io2);  w.l; (* 10 20 30 40 50 60 70 80 90   *)
  a.p1 := io1;  a.p2 := io2;                          Print(a);    w.l; (* 10 21 32 43 54 65 75 85 95   *)
  s.op := Sqr;  s.p := io1;                           Print(s);    w.l; (* 0 1 4 9 16 25                *)
  a.p1 := s;                                          Print(a);    w.l; (* 10 21 34 49 66 85 95 105 115 *)
END Test;

END Jobs.
