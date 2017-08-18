(* PrefixMap - minimalist (hopefully) prefix tree *)
MODULE PrefixMap;
IMPORT Out, Strings;

TYPE

CharBuf = POINTER TO ARRAY OF CHAR;

Atom   = POINTER TO AtomDesc; AtomDesc = RECORD next: Atom END;
Number = POINTER TO RECORD (AtomDesc) n: INTEGER END; (* n is the numeric value *)

(* A Prefix has a character buffer and two forward pointers, next and
   mismatch.
     .  Next is for when the prefix character buffer matches the current
        position of the key
     .  Mismatch points to a Prefix whose character buffer is the next to
        compare with this position in the key.
*)

Prefix* = POINTER TO RECORD (AtomDesc)
  characters: CharBuf;
  mismatch:   Atom;
END;


VAR
  Names: Prefix;

PROCEDURE MakeCharBuf(chars: ARRAY OF CHAR; offset, length: LONGINT): CharBuf;
VAR cb: CharBuf; i: LONGINT;
BEGIN
  IF offset > LEN(chars)-1 THEN RETURN NIL END;
  IF offset + length > LEN(chars)-1 THEN length := LEN(chars) - offset - 1 END;
  NEW(cb, length+1);
  FOR i := 0 TO length-1 DO cb[i] := chars[offset+i] END;
  cb[length] := 0X;
  RETURN cb
END MakeCharBuf;

PROCEDURE ContentLength(cb: CharBuf): LONGINT;
BEGIN IF cb = NIL THEN RETURN 0 ELSE RETURN LEN(cb^)-1 END (* Don't include zero terminator in length *)
END ContentLength;


PROCEDURE Min(a, b: LONGINT): LONGINT;
BEGIN IF a < b THEN RETURN a ELSE RETURN b END
END Min;

(* Returns how many characters in str match characters from source starting at offset *)
PROCEDURE MatchString(VAR source: ARRAY OF CHAR; offset: LONGINT; str: CharBuf): INTEGER;
VAR i: INTEGER; limit: LONGINT;
BEGIN
  limit := Min(ContentLength(str), LEN(source)-1 - offset);
  i := 0; WHILE (i < limit) & (source[i+offset] = str[i]) DO INC(i) END;
  RETURN i
END MatchString;


PROCEDURE Map*(key: CharBuf; a: Atom): Atom;
VAR offset, pl, ml: LONGINT; p: Prefix;
BEGIN
  offset := 0;

  WHILE (a # NIL) & (a IS Prefix) DO
    p := a(Prefix);
    pl := ContentLength(p.characters);
    ml := MatchString(key^, offset, p.characters);
    IF ml > 0 THEN (* some or all of this prefix part matches current position in key *)
      INC(offset, ml); a := p.next;
    ELSE (* none of this prefix part matches current position in key *)
      IF (pl = 0) & (offset = ContentLength(key)) THEN (* matches zero length prefix terminating record *)
        a := p.next
      ELSE
        a:= p.mismatch
      END
    END
  END;

  IF offset < ContentLength(key) THEN RETURN NIL ELSE RETURN a END
END Map;



PROCEDURE NewSuffix(VAR key: ARRAY OF CHAR; offset: LONGINT; target: Atom): Prefix;
VAR i, l: LONGINT; p: Prefix;
BEGIN
  NEW(p); p.next := target; p.mismatch := NIL;
  l := LEN(key) - offset - 1;
  IF l > 0 THEN
    NEW(p.characters, l+1);
    FOR i := 0 TO l-1 DO p.characters[i] := key[i+offset] END;
    p.characters[l] := 0X
  ELSE
    p.characters := NIL
  END;
  RETURN p
END NewSuffix;


PROCEDURE AddInternal(key: CharBuf; offset: LONGINT; target: Atom; VAR a: Atom);
VAR kl, pl, ml: LONGINT; p, q: Prefix;
BEGIN
  kl := ContentLength(key) - offset;
  IF a = NIL THEN
    a := NewSuffix(key^, offset, target)
  ELSIF ~(a IS Prefix) THEN
    p := NewSuffix(key^, offset, target);
    NEW(q); q.characters := NIL; q.next := a; q.mismatch := p;
    a := q;
  ELSE
    p := a(Prefix);
    pl := ContentLength(p.characters);
    IF pl = 0 THEN (* Special case of empty prefix at end of key *)
      IF offset = ContentLength(key) THEN
        AddInternal(key, offset, target, p.next)
      ELSE
        AddInternal(key, offset, target, p.mismatch)
      END
    ELSE
      ml := MatchString(key^, offset, p.characters);
      IF ml = pl THEN (* all this prefix part matches current position in key *)
        AddInternal(key, offset+ml, target, p.next)
      ELSIF ml > 0 THEN (* some of this prefix part matches current position in key *)
        (* Split prefix into two parts and try again at second part *)
        NEW(q); q.characters := MakeCharBuf(p.characters^, ml, pl-ml);
        p.characters := MakeCharBuf(p.characters^, 0, ml);
        q.mismatch := NIL; q.next := p.next;
        p.next := q; AddInternal(key, offset+ml, target, p.next)
      ELSE (* none of this prefix part matches current position in key *)
        AddInternal(key, offset, target, p.mismatch)
      END
    END
  END
END AddInternal;


PROCEDURE Add*(key: CharBuf; target: Atom);
VAR a: Atom;
BEGIN a := Names; AddInternal(key, 0, target, a); Names := a(Prefix)
END Add;





(* --------------------------Testing ------------------------- *)

PROCEDURE MakeNumber(i: INTEGER): Number;
VAR n: Number;
BEGIN  NEW(n);  n.next := NIL;  n.n := i;  RETURN n
END MakeNumber;

PROCEDURE DumpPrefixTree(p: Prefix; depth: LONGINT);
VAR i: LONGINT;
BEGIN
  IF p.characters = NIL THEN Out.String("''") ELSE Out.String(p.characters^) END;
  IF    p.next = NIL     THEN Out.Ln
  ELSIF p.next IS Prefix THEN DumpPrefixTree(p.next(Prefix), depth + ContentLength(p.characters))
  ELSE  Out.String(" -> "); Out.Int(p.next(Number).n,1); Out.Ln
  END;
  IF p.mismatch # NIL THEN
    FOR i := 0 TO depth-1 DO Out.Char(' ') END;
    DumpPrefixTree(p.mismatch(Prefix), depth)
  END
END DumpPrefixTree;


PROCEDURE TestLookup(s: ARRAY OF CHAR; i: INTEGER);
VAR cb: CharBuf; a: Atom;
BEGIN
  cb := MakeCharBuf(s, 0, LEN(s)-1);
  Out.String("Lookup "); Out.String(s); Out.String(" -> ");
  a := Map(cb, Names);
  IF a = NIL THEN Out.String("not found.") ELSE Out.Int(a(Number).n,1)END; Out.Ln;
END TestLookup;

PROCEDURE TestAddLookup(s: ARRAY OF CHAR; i: INTEGER);
VAR cb: CharBuf; a: Atom;
BEGIN
  cb := MakeCharBuf(s, 0, LEN(s)-1);
  Out.String("Adding "); Out.String(s); Out.Char(':'); Out.Ln;
  Add(cb, MakeNumber(i));
  Out.String("  "); DumpPrefixTree(Names, 2);
  TestLookup(s, i)
END TestAddLookup;

BEGIN
  TestAddLookup("Hello",     1);
  TestAddLookup("Greetings", 2);
  TestAddLookup("Salaam",    3);
  TestAddLookup("Greenery",  4);
  TestAddLookup("Greening",  5);
  TestAddLookup("Greedy",    6);
  TestAddLookup("Heavy",     7);
  TestAddLookup("Heavyside", 8);
  TestAddLookup("Holding",   9);
  TestAddLookup("Hold",     10);
  TestAddLookup("He",        11);
  TestAddLookup("Henge",     12);
  TestAddLookup("Holder",    13);

  TestLookup("Hello",     1);
  TestLookup("Greetings", 2);
  TestLookup("Salaam",    3);
  TestLookup("Greenery",  4);
  TestLookup("Greening",  5);
  TestLookup("Greedy",    6);
  TestLookup("Heavy",     7);
  TestLookup("Heavyside", 8);
  TestLookup("Holding",   9);
  TestLookup("Hold",      10);
  TestLookup("He",        11);
  TestLookup("Henge",     12);
  TestLookup("Holder",    13);
END PrefixMap .
