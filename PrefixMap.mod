(* PrefixMap - minimalist (hopefully) prefix tree *)
MODULE PrefixMap;
IMPORT Out, Strings, Files;

TYPE

CharBuf = POINTER TO ARRAY OF CHAR;

Atom   = POINTER TO AtomDesc; AtomDesc = RECORD next: Atom END;
Number = POINTER TO RECORD (AtomDesc) n: INTEGER END; (* n is the numeric value *)
Chars  = POINTER TO RECORD (AtomDesc) c: CharBuf END;
Fork   = POINTER TO RECORD (AtomDesc) other: Atom END;



VAR
  Names: Atom;
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
PROCEDURE wi (i: LONGINT); BEGIN wbreak(ChClass, 0); Out.Int(i,1); ChClass := 0 END wi;

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Internal error:"); wsl(msg); HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;

(* -------------------------------- Debug --------------------------------- *)


PROCEDURE WriteAtom(a: Atom);
BEGIN
  IF a = NIL THEN ws("NIL")
  ELSE WITH
    a: Number    DO ws("N:"); wnb; wi(a.n); ws(".");
  | a: Chars     DO ws("C:"); wnb; wc('"'); ws(a.c^); wc('"'); ws(".");
  | a: Fork     DO ws("Fork.")
  ELSE wsl("Unrecognised")
  END END;
END WriteAtom;

PROCEDURE DumpAtom(a: Atom);
BEGIN WriteAtom(a); wl
END DumpAtom;

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


PROCEDURE FindInternal(key: CharBuf; offset: LONGINT; root: Atom): Atom;
VAR result: Atom; matchLength: LONGINT;
BEGIN
  result := NIL;
  IF offset >= ContentLength(key) THEN
    result := root
  ELSIF root # NIL THEN
    IF root IS Fork THEN
      result := FindInternal(key, offset, root.next);
      IF result = NIL THEN result := FindInternal(key, offset, root(Fork).other) END
    ELSIF root IS Chars THEN
      matchLength := MatchString(key, offset, root(Chars).c);
      IF matchLength = ContentLength(root(Chars).c) THEN
        result := FindInternal(key, offset+matchLength, root.next)
      END
    END
  END;
  RETURN result
END FindInternal;

PROCEDURE Find*(key: CharBuf; root: Atom): Atom;
BEGIN RETURN FindInternal(key, 0, root)
END Find;

PROCEDURE InsertSplit(key: CharBuf; offset: LONGINT; target: Atom; VAR a: Atom);
VAR suffix: Atom; c: Chars; s: Fork; keyLength: LONGINT;
BEGIN
  (*ws("InsertSplit key"); ws(key^); ws(", offset"); wi(offset); ws(", a"); DumpAtom(a);*)
  keyLength := ContentLength(key);
  IF offset < keyLength THEN
    NEW(c);  suffix := c;
    c.c := MakeCharBuf(key^, offset, keyLength-offset);  c.next := target
  ELSE
    suffix := target;
  END;
  NEW(s);  s.other := a;  s.next := suffix;  a := s
END InsertSplit;

PROCEDURE StoreInternal(key: CharBuf; offset: LONGINT; target: Atom; VAR current: Atom): BOOLEAN;
VAR matchLength: LONGINT; result: BOOLEAN; keyLength, curLength: LONGINT;  c: Chars;
BEGIN
  (*ws("StoreInternal key"); ws(key^); ws(", offset"); wi(offset); ws(", current"); DumpAtom(current);*)
  keyLength := ContentLength(key);
  IF offset >= keyLength THEN (* Key already exists. Insert target as an alternative *)
    (*wsl("offset >= keyLength");*)
    InsertSplit(key, offset, target, current);
    RETURN TRUE
  ELSIF current = NIL THEN
    (*wsl("Nil");*)
    InsertSplit(key, offset, target, current);
    RETURN TRUE
  ELSIF current IS Fork THEN
    (*wsl("Fork, try next");*)
    IF ~StoreInternal(key, offset, target, current.next) THEN
      (*wsl("  next failed, try alternate.");*)
      IF current(Fork).other # NIL THEN
        (*wsl("  alternate is non-nil, store here.");*)
        RETURN StoreInternal(key, offset, target, current(Fork).other)
      ELSE
        (*wsl("  alternate is nil, insert Fork here.");*)
        InsertSplit(key, offset, target, current(Fork).other)
      END
    END;
    RETURN TRUE
  ELSIF current IS Chars THEN
    matchLength := MatchString(key, offset, current(Chars).c);
    curLength := ContentLength(current(Chars).c);
    (*ws("Chars: matchLength"); wi(matchLength); ws(", curLength"); wi(curLength); wl;*)
    IF matchLength = 0 THEN
      RETURN FALSE
    ELSE
      IF matchLength < curLength THEN (* Fork this node *)
        NEW(c); c.next := current.next; c.c := MakeCharBuf(current(Chars).c^, matchLength, curLength-matchLength);
        current(Chars).next := c; current(Chars).c := MakeCharBuf(current(Chars).c^, 0, matchLength);
        InsertSplit(key, offset+matchLength, target, current.next);
        RETURN TRUE
      ELSE
        RETURN StoreInternal(key, offset+matchLength, target, current.next)
      END
    END
  ELSE
    InsertSplit(key, offset, target, current);
    RETURN TRUE
  END
END StoreInternal;

PROCEDURE Store*(key: CharBuf; target: Atom; VAR root: Atom);
BEGIN ASSERT(StoreInternal(key, 0, target, root))
END Store;




(* --------------------------Testing ------------------------- *)


PROCEDURE MakeNumber(i: INTEGER): Number;
VAR n: Number;
BEGIN  NEW(n);  n.next := NIL;  n.n := i;  RETURN n
END MakeNumber;

PROCEDURE WritePrefixTree(p: Atom; indent: LONGINT);
VAR i: LONGINT;
BEGIN
  IF p # NIL THEN
    IF p IS Chars THEN
      ws(p(Chars).c^); wnb;
      WritePrefixTree(p.next, indent+ContentLength(p(Chars).c))
    ELSIF p IS Fork THEN
      WritePrefixTree(p.next, indent); wl;
      FOR i := 0 TO indent-1 DO wc(' ') END;
      WritePrefixTree(p(Fork).other, indent);
    END
  END
END WritePrefixTree;

PROCEDURE wspace(i: LONGINT);
BEGIN WHILE i > 0 DO wc(' '); DEC(i) END
END wspace;

PROCEDURE DumpPrefixTree(p: Atom; indent: LONGINT);
VAR i: LONGINT;
BEGIN
  IF p = NIL THEN
    ws("<nil>")
  ELSIF p IS Chars  THEN
    ws(p(Chars).c^); wnb;
    DumpPrefixTree(p.next, indent+ContentLength(p(Chars).c))
  ELSIF p IS Number THEN
    ws("#"); wnb; wi(p(Number).n);
    DumpPrefixTree(p.next, indent+2)
  ELSIF p IS Fork THEN
    ws("|"); INC(indent); DumpPrefixTree(p.next, indent); wl;
    wspace(indent);       DumpPrefixTree(p(Fork).other, indent);
  END
END DumpPrefixTree;


PROCEDURE SkipToNumber(a: Atom): Atom;
VAR b: Atom;
BEGIN
  IF (a = NIL) OR ~(a IS Fork) THEN RETURN a
  ELSE
    b := SkipToNumber(a.next);
    (*IF (b = NIL) OR ~(b IS Fork) THEN RETURN b*)
    IF (b = NIL) OR (b IS Number) THEN RETURN b
    ELSE RETURN SkipToNumber(a(Fork).other)
    END
  END
END SkipToNumber;

PROCEDURE TestLookup(s: ARRAY OF CHAR);
VAR cb: CharBuf; a: Atom;
BEGIN
  cb := MakeCharBuf(s, 0, LEN(s)-1);
  wlc; Out.String("Lookup "); Out.String(s); Out.String(" -> ");
  a := SkipToNumber(Find(cb, Names));
  IF a = NIL THEN Out.String("not found.")
  ELSIF a IS Number THEN
    Out.Int(a(Number).n,1); Out.Ln;
  ELSE
    wsl("found non-number:");  ws("  "); DumpPrefixTree(a, 2)
  END
END TestLookup;

PROCEDURE TestAddLookup(s: ARRAY OF CHAR; i: INTEGER);
VAR cb: CharBuf; a: Atom;
BEGIN
  cb := MakeCharBuf(s, 0, LEN(s)-1);
  Out.String("Adding "); Out.String(s); Out.Char(':'); Out.Ln;
  Store(cb, MakeNumber(i), Names);
  wsl("Names:"); ws("  "); DumpPrefixTree(Names, 2);
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
        cb := MakeCharBuf(line, 0, l);  Store(cb, MakeNumber(i), Names);  INC(i);
      END
    END
  END;
  wi(i); wsl("strings loaded:");
  DumpPrefixTree(Names, 0);
END TestFileLoad;

BEGIN
  Abort := FALSE;  ChClass := 3;  Names := NIL;

  TestAddLookup("Hello",     1);
  TestAddLookup("Hellooo",   99);
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
  (*
  TestFileLoad;
  *)
END PrefixMap.
