(* PrefixMap - minimalist (hopefully) prefix tree *)
MODULE PrefixMap;
IMPORT Out, Strings, Files;

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
  Abort: BOOLEAN;


(* ---------------------------- Console output ---------------------------- *)

  ChClass: INTEGER; (* 0 letter, 1 non-letter, 2 eol *)

PROCEDURE Classify(ch: CHAR): INTEGER;
BEGIN
  CASE ch OF
    'a'..'z', 'A'..'Z', '0'..'9':      RETURN 0 (* Space may be required required before and after*)
  | ',', '.', ';', ':', '}', ']', ')': RETURN 1 (* No space needed before, space may be required after *)
  | 0DX, 0AX:                          RETURN 3 (* End of line *)
  ELSE                                 RETURN 2 (* No space needed before or after *)
  END
END Classify;

PROCEDURE wbreak(c1, c2: INTEGER); BEGIN
  CASE c1 OF
    0: IF c2 > 0 THEN RETURN END
  | 1: IF c2 > 1 THEN RETURN END
  ELSE RETURN
  END;
  Out.Char(' ')
END wbreak;

PROCEDURE wnb; BEGIN ChClass := 2 END wnb;

PROCEDURE ws(s: ARRAY OF CHAR);
VAR l: INTEGER;
BEGIN
  l := Strings.Length(s);
  IF l > 0 THEN wbreak(ChClass, Classify(s[0])); Out.String(s); ChClass := Classify(s[l-1]) END
END ws;

PROCEDURE wc(c: CHAR);           BEGIN Out.Char(c); ChClass := 2                END wc;
PROCEDURE wl;                    BEGIN Out.Ln; ChClass := 3                     END wl;
PROCEDURE wlc;                   BEGIN IF ChClass < 3 THEN wl END               END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl                                END wsl;
PROCEDURE wi (i: LONGINT); BEGIN wbreak(ChClass, 0); Out.Int(i,1); ChClass := 1 END wi;

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Internal error:"); wsl(msg); HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


(* ----------------------------- Atom basics ------------------------------ *)



PROCEDURE MakeCharBuf(VAR source: ARRAY OF CHAR; offset, length: LONGINT): CharBuf;
VAR cb: CharBuf; i, sourceLength: LONGINT;
BEGIN
  sourceLength := Strings.Length(source);
  IF offset + length > sourceLength THEN length := sourceLength - offset END;
  IF length <= 0 THEN RETURN NIL END;

  NEW(cb, length+1);
  FOR i := 0 TO length-1 DO cb[i] := source[offset+i] END;
  cb[length] := 0X;
  RETURN cb
END MakeCharBuf;

PROCEDURE ContentLength(cb: CharBuf): LONGINT;
BEGIN IF cb = NIL THEN RETURN 0 ELSE RETURN LEN(cb^)-1 END (* Don't include zero terminator in length *)
END ContentLength;


(* Returns how many characters in str match characters from source starting at offset *)
PROCEDURE MatchString(source: CharBuf; offset: LONGINT; str: CharBuf): INTEGER;
VAR i: INTEGER; limit, sourceLength: LONGINT;
BEGIN
  sourceLength := ContentLength(source);
  limit := ContentLength(str);
  IF (offset >= sourceLength) OR (limit <= 0) THEN RETURN 0 END;
  IF sourceLength-offset < limit THEN limit := sourceLength-offset END;
  i := 0; WHILE (i < limit) & (source[i+offset] = str[i]) DO INC(i) END;
  RETURN i
END MatchString;


PROCEDURE Find*(key: CharBuf; a: Atom): Atom;
VAR offset, pl, ml: LONGINT; p: Prefix;
BEGIN
  offset := 0;
  WHILE (a # NIL) & (a IS Prefix) DO
    p := a(Prefix);
    pl := ContentLength(p.characters);
    ml := MatchString(key, offset, p.characters);
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
END Find;


PROCEDURE StoreInternal(key: CharBuf; offset: LONGINT; target: Atom; VAR a: Atom);
VAR kl, pl, ml: LONGINT; p, q: Prefix;
BEGIN
  kl := ContentLength(key) - offset;  p := NIL;  pl := 0;  ml := 0;
  IF (a # NIL) & (a IS Prefix) THEN
    p := a(Prefix);  pl := ContentLength(p.characters)
  END;
  IF p = NIL THEN
    NEW(p); p.next := target; p.mismatch := NIL;
    p.characters := MakeCharBuf(key^, offset, kl);
    IF a = NIL THEN a := p
    ELSE NEW(q); q.characters := NIL; q.next := a; q.mismatch := p; a := q;
    END
  ELSIF (pl = 0) & (kl = 0) THEN
    StoreInternal(key, offset, target, p.next)
  ELSE
    ml := MatchString(key, offset, p.characters);
    IF ml = 0 THEN
      StoreInternal(key, offset, target, p.mismatch)
    ELSE
      IF ml < pl THEN
        (* Split prefix into two parts and try again at second part *)
        NEW(q); q.characters := MakeCharBuf(p.characters^, ml, pl-ml);
        p.characters := MakeCharBuf(p.characters^, 0, ml);
        q.mismatch := NIL; q.next := p.next;
        p.next := q;
      END;
      StoreInternal(key, offset+ml, target, p.next)
    END
  END;
END StoreInternal;

PROCEDURE Store*(key: CharBuf; target: Atom);
VAR a: Atom;
BEGIN a := Names; StoreInternal(key, 0, target, a); Names := a(Prefix)
END Store;





(* --------------------------Testing ------------------------- *)

PROCEDURE MakeNumber(i: INTEGER): Number;
VAR n: Number;
BEGIN  NEW(n);  n.next := NIL;  n.n := i;  RETURN n
END MakeNumber;

PROCEDURE DumpPrefixTree(p: Prefix; depth: LONGINT);
CONST verbose = FALSE;
VAR i, indent: LONGINT;
BEGIN
  IF verbose THEN
    ws("'"); wnb; IF p.characters # NIL THEN Out.String(p.characters^); wnb END;
    ws("' "); wnb;
    indent := depth + ContentLength(p.characters) + 3;
  ELSE
    IF p.characters = NIL THEN Out.String("''") ELSE Out.String(p.characters^) END;
    indent := depth + ContentLength(p.characters);
  END;
  IF    p.next = NIL     THEN Out.Ln
  ELSIF p.next IS Prefix THEN DumpPrefixTree(p.next(Prefix), indent)
  ELSE  Out.String(" -> "); Out.Int(p.next(Number).n,1); Out.Ln
  END;
  IF p.mismatch # NIL THEN
    FOR i := 0 TO depth-1 DO Out.Char(' ') END;
    DumpPrefixTree(p.mismatch(Prefix), depth)
  END
END DumpPrefixTree;


PROCEDURE PrintKeysInternal(p: Prefix; VAR leadin: ARRAY OF CHAR);
VAR i: INTEGER; localLeadin: ARRAY 200 OF CHAR;
BEGIN
  localLeadin := leadin;
  IF p.characters # NIL THEN Strings.Append(p.characters^, localLeadin) END;

  IF    p.next = NIL     THEN wsl(localLeadin)
  ELSIF p.next IS Prefix THEN PrintKeysInternal(p.next(Prefix), localLeadin)
  ELSE  wsl(localLeadin);
  END;

  IF p.mismatch # NIL THEN
    PrintKeysInternal(p.mismatch(Prefix), leadin)
  END
END PrintKeysInternal;

PROCEDURE PrintKeys;
VAR leadin: ARRAY 200 OF CHAR;
BEGIN leadin := ""; PrintKeysInternal(Names, leadin)
END PrintKeys;


PROCEDURE TestLookup(s: ARRAY OF CHAR);
VAR cb: CharBuf; a: Atom;
BEGIN
  cb := MakeCharBuf(s, 0, LEN(s)-1);
  Out.String("Lookup "); Out.String(s); Out.String(" -> ");
  a := Find(cb, Names);
  IF a = NIL THEN Out.String("not found.") ELSE Out.Int(a(Number).n,1)END; Out.Ln;
END TestLookup;

PROCEDURE TestAddLookup(s: ARRAY OF CHAR; i: INTEGER);
VAR cb: CharBuf; a: Atom;
BEGIN
  cb := MakeCharBuf(s, 0, LEN(s)-1);
  Out.String("Adding "); Out.String(s); Out.Char(':'); Out.Ln;
  Store(cb, MakeNumber(i));
  Out.String("  "); DumpPrefixTree(Names, 2);
  TestLookup(s)
END TestAddLookup;

PROCEDURE TestFileLoad;
VAR f: Files.File; r: Files.Rider; line: ARRAY 200 OF CHAR;
    i, l: INTEGER; cb: CharBuf;
BEGIN
  f := Files.Old("strings"); i := 0;
  IF f # NIL THEN
    Files.Set(r, f, 0);
    WHILE ~r.eof DO
      Files.ReadLine(r, line); l := Strings.Length(line);
      WHILE (l>0) & (line[l-1]=' ') DO DEC(l) END;
      IF l > 0 THEN
        (*ws("Adding:"); wsl(line);*)
        cb := MakeCharBuf(line, 0, l);  Store(cb, MakeNumber(i));  INC(i);
      END
    END
  END;
  wi(i); wsl("strings loaded:");
  (*DumpPrefixTree(Names, 0);*)
  PrintKeys
END TestFileLoad;

BEGIN
  Abort := FALSE;  ChClass := 3;
  (*
  TestAddLookup("Hello",     1);
  TestAddLookup("Greetings", 2);
  TestAddLookup("Salaam",    3);
  TestAddLookup("Greenery",  4);
  TestAddLookup("Greening",  5);
  TestAddLookup("Greedy",    6);
  TestAddLookup("Heavy",     7);
  TestAddLookup("Heavyside", 8);
  TestAddLookup("Holding",   9);
  TestAddLookup("Hold",      10);
  TestAddLookup("He",        11);
  TestAddLookup("Henge",     12);
  TestAddLookup("Holder",    13);
  Out.Ln;
  TestLookup("Hello");
  TestLookup("Greetings");
  TestLookup("Salaam");
  TestLookup("Greenery");
  TestLookup("Greening");
  TestLookup("Greedy");
  TestLookup("Heavy");
  TestLookup("Heavyside");
  TestLookup("Holding");
  TestLookup("Hold");
  TestLookup("He");
  TestLookup("Henge");
  TestLookup("Holder");
  Out.Ln;
  TestLookup("Holder");
  TestLookup("Henge");
  TestLookup("He");
  TestLookup("Hold");
  TestLookup("Holding");
  TestLookup("Heavyside");
  TestLookup("Heavy");
  TestLookup("Greedy");
  TestLookup("Greening");
  TestLookup("Greenery");
  TestLookup("Salaam");
  TestLookup("Greetings");
  TestLookup("Hello");
  *)
  TestFileLoad;
END PrefixMap.
