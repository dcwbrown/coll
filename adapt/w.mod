MODULE w;  (* Console write convenience functions. *)

IMPORT TextWriter;

CONST MaxLines = 8000;
VAR  LineCount: INTEGER;

PROCEDURE^ Fail*(msg: ARRAY OF CHAR);

PROCEDURE s*(s: ARRAY OF CHAR);  BEGIN TextWriter.String(s)            END s;
PROCEDURE c*(c: CHAR);           BEGIN TextWriter.Char(c)              END c;
PROCEDURE i*(i: LONGINT);        BEGIN TextWriter.Integer(i)           END i;
PROCEDURE x*(i,n: LONGINT);      BEGIN TextWriter.Hex(i,n)             END x;
PROCEDURE nb*;                   BEGIN TextWriter.NoBreak              END nb;
PROCEDURE lc*;                   BEGIN TextWriter.StartLine            END lc;
PROCEDURE fl*;                   BEGIN TextWriter.Flush                END fl;
PROCEDURE sl*(c: ARRAY OF CHAR); BEGIN s(c); TextWriter.NewLine        END sl;
PROCEDURE space(i: LONGINT);     BEGIN WHILE i>0 DO c(' '); DEC(i) END END space;
PROCEDURE b*(b: BOOLEAN);        BEGIN IF b THEN s("TRUE") ELSE s("FALSE") END END b;

PROCEDURE l*;
BEGIN
  TextWriter.NewLine;  INC(LineCount);
  IF LineCount > MaxLines THEN LineCount := 0; Fail("LineCount exceeded.") END
END l;

PROCEDURE wut(u: LONGINT; n: INTEGER);
BEGIN
  IF n > 1 THEN wut(u DIV 64, n-1) END;
  c(CHR(u MOD 64 + 080H))
END wut;

PROCEDURE u*(u: LONGINT);  (* Write Unicode codepoint as UTF-8 *)
BEGIN
  IF    u < 0       THEN s('^-'); x(-u,1)
  ELSIF u = 10      THEN l  (* LF *)
  ELSIF u < 32      THEN c('^'); x(u,1)
  ELSIF u < 000080H THEN c(CHR(u))
  ELSIF u < 000800H THEN c(CHR(u DIV 00040H + 0C0H));  wut(u, 1)
  ELSIF u < 010000H THEN c(CHR(u DIV 01000H + 0E0H));  wut(u, 2)
  ELSIF u < 110000H THEN c(CHR(u DIV 40000H + 0F0H));  wut(u, 3)
  ELSE Fail("Write unicode value > 10FFFFH.")
  END
END u;


PROCEDURE Fail*(msg: ARRAY OF CHAR);
BEGIN IF msg[0] # 0X THEN lc; s("Internal failure:"); sl(msg) END;
  lc; HALT(99)
END Fail;

PROCEDURE Assert*(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN lc; s("Assertion failure:"); sl(msg); HALT(99) END
END Assert;


BEGIN
  LineCount := 0
END w.

