(* PrefixMap - minimalist (hopefully) prefix tree *)
MODULE PrefixMap;
IMPORT Out, Strings, Files;

TYPE

CharBuf = POINTER TO ARRAY OF CHAR;

Atom   = POINTER TO AtomDesc; AtomDesc = RECORD next: Atom END;
Number = POINTER TO RECORD (AtomDesc) value: LONGINT END; (* value is the numeric value *)
Text   = POINTER TO RECORD (AtomDesc) text:  CharBuf END;
Fork   = POINTER TO RECORD (AtomDesc) other: Atom END;






(*  Rover - describes a pair of adjacent positions

    prev IS Number: next is prev.next
    prev IS Text:  prev offset is pos, pos+1 implies next position
    prev IS Fork:   pos = 0 => next is prev.next, pos=1 => next is prev.other
*)
Rover = RECORD
          prev: Atom;
          pos:  LONGINT
          (* stack: Atom - stack of retun continuation points coreesponding to previous Nest atoms *)
        END;

(* Crawler - obsolete overengineered versin of Rover *)

Crawler = RECORD
            prevAtom: Atom;  prevOffset: LONGINT;
            currAtom: Atom;  currOffset: LONGINT
          END;



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
    a: Number DO ws("N-"); wi(a.value); ws(".");
  | a: Text  DO ws("C-"); wc('"'); ws(a.text^); wc('"'); ws(".");
  | a: Fork   DO ws("Fork.")
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
RETURN cb END MakeCharBuf;


PROCEDURE MakeText(c: ARRAY OF CHAR): Text;
VAR s: Text;
BEGIN
  NEW(s); s.next := NIL;
  NEW(s.text, Strings.Length(c)+1);  COPY(c, s.text^);
RETURN s END MakeText;


PROCEDURE ContentLength(cb: CharBuf): LONGINT;
BEGIN IF cb = NIL THEN RETURN 0 ELSE RETURN LEN(cb^)-1 END (* Don't include zero terminator in length *)
END ContentLength;

PROCEDURE MakeString(c: ARRAY OF CHAR): Text;
VAR s: Text;
BEGIN
  NEW(s); s.next := NIL;
  NEW(s.text, Strings.Length(c)+1);  COPY(c, s.text^);
RETURN s END MakeString;


(* --------------------- Rovers ------------------- *)

PROCEDURE MakeRover(a: Atom; VAR r: Rover);
BEGIN r.prev := a;  r.pos := 0
END MakeRover;


PROCEDURE NextPos(VAR a: Atom; VAR p: LONGINT);
VAR al: Atom;
BEGIN
  Assert(a # NIL, "NextPos expects non-nil atom");
  Assert((a IS Number) OR (a IS Text) OR (a IS Fork), "NextPos exptects number, text or fork");
  al := a;
  WITH
    al: Number DO a := a.next; p := 0
  | al: Text   DO IF p < ContentLength(al.text) THEN INC(p) ELSE a := a.next; p := 0 END
  | al: Fork   DO IF p = 0 THEN a := a.next ELSE a := al.other END; p := 0
  END
END NextPos;

PROCEDURE MatchRover(VAR r1, r2: Rover): BOOLEAN;
(* Return whether r1 and r2 are at a matching position *)
VAR a1, a2: Atom; p1, p2: LONGINT;
BEGIN
  a1 := r1.prev;  p1 := r1.pos;  NextPos(a1, p1);
  a2 := r2.prev;  p2 := r2.pos;  NextPos(a2, p2);
  Assert((a1 IS Text) OR (a1 IS Number), "MatchRover expects r1 to be Text or Number");
  Assert((a2 IS Text) OR (a2 IS Number), "MatchRover expects r2 to be Text or Number");
  WITH
    a1: Number DO RETURN (a2 IS Number) & (a1.value = a2(Number).value)
  | a1: Text   DO RETURN (a2 IS Text) & (a1.text[p1] = a2(Text).text[p2])
  END
END MatchRover;



PROCEDURE MatchCrawler(r1: Crawler; VAR r2: Crawler): BOOLEAN;
(* Returns whether the current character or atom in r1 and r2 match.
   If r2.a is a Fork, then both sides of the fork are tested (recusively) and
   if a maatch is found then r2 is advanced to the macth.
   Notes - does not (currently) support r1 being a Fork.
*)
VAR n2: Crawler;
BEGIN
  IF r2.currAtom = NIL THEN RETURN r1.currAtom = NIL END;

  IF (r1.currAtom = NIL) & ~(r2.currAtom IS Fork) THEN RETURN FALSE END;

  Assert((r1.currAtom = NIL) OR ~(r1.currAtom IS Fork), "MatchCrawler does not support forks in r1.");

  IF    r2.currAtom IS Text  THEN  RETURN (r1.currAtom IS Text)  & (r1.currAtom(Text).text[r1.currOffset] = r2.currAtom(Text).text[r2.currOffset])
  ELSIF r2.currAtom IS Number THEN  RETURN (r1.currAtom IS Number) & (r1.currAtom(Number).value              = r2.currAtom(Number).value)
  ELSIF r2.currAtom IS Fork   THEN
    n2.prevOffset := n2.currOffset; n2.currOffset := 0;
    n2.prevAtom   := n2.currAtom;   n2.currAtom   := r2.currAtom.next;
    IF MatchCrawler(r1, n2) THEN  r2 := n2;  RETURN TRUE;
    ELSE
      n2.currAtom := r2.currAtom(Fork).other;
      IF MatchCrawler(r1, n2) THEN  r2 := n2;  RETURN TRUE;
      END
    END
  END;

  RETURN FALSE
END MatchCrawler;


PROCEDURE AdvanceCrawler(VAR r: Crawler);
BEGIN
  ASSERT((r.currAtom IS Text) OR (r.currAtom IS Number));
  IF (r.currAtom IS Text) & (r.currOffset < ContentLength(r.currAtom(Text).text)-1) THEN
    r.prevOffset := r.currOffset;  INC(r.currOffset)
  ELSE
    r.prevAtom := r.currAtom;       r.prevOffset := r.currOffset;
    r.currAtom := r.currAtom.next;  r.currOffset := 0
  END
END AdvanceCrawler;


PROCEDURE SplitChars(VAR r: Crawler);
VAR offset, length: LONGINT;  c: Text;
BEGIN
  Assert((r.currAtom # NIL) & (r.currAtom IS Text), "SplitChars expected r.currAtom to be Text");
  offset := r.currOffset;  length := ContentLength(r.currAtom(Text).text);
  Assert(offset > 0, "SplitChars expected current offset to be greater than zero");
  Assert(offset < length, "SplitChars expected current offset to be less than length");

  r.prevAtom := r.currAtom;  r.prevOffset := offset - 1;
  NEW(c);  c.next := r.currAtom.next;
  r.prevAtom.next := c;  r.currAtom := c;  r.currOffset := 0;

  r.currAtom(Text).text := MakeCharBuf(r.prevAtom(Text).text^, offset, length-offset);
  r.prevAtom(Text).text := MakeCharBuf(r.prevAtom(Text).text^, 0, offset);
END SplitChars;


PROCEDURE MatchAtoms(add: BOOLEAN; VAR r1, r2: Crawler);
(*  Scans r1 and r2 forward whilst a match is achievable.
**
**  On exit rovers r1 and r2 point to the first non-matching atom.
**  If the mismatch is in the middle of a Text, the corresponding Crawler's .o
**  field identifies the exact mismatch positon.
**
**  If the add parameter is passed as TRUE and a mismatch occurs befor the
**  end of r1, then the remainder of r1 is inserted as a fork in r2.
**
*)
VAR f: Fork;
BEGIN
  WHILE MatchCrawler(r1, r2) DO  AdvanceCrawler(r1);  AdvanceCrawler(r2)  END;
  IF add & (r1.currAtom # NIL) THEN (* Insert remainder of r1 as fork in r2 *)
    IF (r1.currAtom IS Text) & (r1.currOffset > 0) THEN SplitChars(r1) END;
    IF r2.currAtom = NIL THEN
      r2.prevAtom.next := r1.currAtom
    ELSE
      IF (r2.currAtom IS Text) & (r2.currOffset > 0) THEN SplitChars(r2) END;
      (* Insert fork between p2 and r2, with new content from r1 as the other part *)
      NEW(f);  f.next := r2.currAtom;  r2.prevAtom.next := f;  f.other := r1.currAtom;
    END
  END
END MatchAtoms;


PROCEDURE SetCrawler(a1: Atom; o1: LONGINT; a2: Atom; o2: LONGINT; VAR r: Crawler);
BEGIN  r.prevAtom := a1;  r.prevOffset := o1;  r.currAtom := a2;  r.currOffset := o2;
END SetCrawler;


PROCEDURE Find*(key: Atom; VAR result: Crawler);
VAR rkey: Crawler;
BEGIN
  SetCrawler(NIL, 0, key, 0, rkey);
  MatchAtoms(FALSE, rkey, result);
  IF rkey.currAtom # NIL THEN result.currAtom := NIL END
END Find;




(* --------------------------Testing ------------------------- *)


PROCEDURE MakeNumber(i: INTEGER): Number;
VAR n: Number;
BEGIN  NEW(n);  n.next := NIL;  n.value := i;  RETURN n
END MakeNumber;

PROCEDURE WritePrefixTree(p: Atom; indent: LONGINT);
VAR i: LONGINT;
BEGIN
  IF p # NIL THEN
    IF p IS Text THEN
      IF p(Text).text # NIL THEN ws(p(Text).text^); wnb END;
      WritePrefixTree(p.next, indent+ContentLength(p(Text).text))
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
  ELSIF p IS Text  THEN
    IF p(Text).text # NIL THEN ws(p(Text).text^); wnb END;
    DumpPrefixTree(p.next, indent+ContentLength(p(Text).text))
  ELSIF p IS Number THEN
    ws("#"); wnb; wi(p(Number).value);
    DumpPrefixTree(p.next, indent+2)
  ELSIF p IS Fork THEN
    ws("|"); INC(indent); DumpPrefixTree(p.next, indent); wl;
    wspace(indent);       DumpPrefixTree(p(Fork).other, indent);
  END
END DumpPrefixTree;


PROCEDURE SkipToNumber(a: Atom): Atom;
VAR b: Atom;
BEGIN
  IF    a = NIL     THEN RETURN NIL
  ELSIF a IS Number THEN RETURN a
  ELSIF a IS Fork   THEN
    b := SkipToNumber(a(Fork).next);
    IF b = NIL THEN b := SkipToNumber(a(Fork).other) END;
    RETURN b
  ELSE
    RETURN NIL
  END
END SkipToNumber;

PROCEDURE TestLookup(s: ARRAY OF CHAR);
VAR str: Text; a: Atom; r1, r2: Crawler;
BEGIN
  str := MakeText(s);
  wlc; ws("Lookup "); ws(s); ws(" -> ");
  SetCrawler(Names, 0, Names.next, 0, r1);
  Find(str, r1);
  a := SkipToNumber(r1.currAtom);
  IF a = NIL THEN wsl("not found.")
  ELSIF a IS Number THEN
    wi(a(Number).value); wl;
  ELSE
    wsl("found non-number:");  ws("  "); DumpPrefixTree(a, 2)
  END;
END TestLookup;

PROCEDURE TestAddLookup(s: ARRAY OF CHAR; i: INTEGER);
VAR c: Text; n: Number;  r1, r2: Crawler;
BEGIN
  IF Names = NIL THEN (* Create an empty anchoring Text at the root of the tree *)
    NEW(c);  c.text := NIL;  c.next := NIL;  Names := c
  END;

  NEW(c); c.text := MakeCharBuf(s, 0, LEN(s)-1);
  NEW(n); n.value := i;
  c.next := n;  n.next := NIL;

  ws("Adding "); ws(s); wc(':'); wl;


  SetCrawler(NIL, 0, c, 0, r1);
  SetCrawler(Names, 0, Names.next, 0, r2);
  MatchAtoms(TRUE, r1, r2);

  wsl("Names:"); ws("  "); DumpPrefixTree(Names, 2);
  ws(".."); WritePrefixTree(Names, 2);

  TestLookup(s)
END TestAddLookup;


(*
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
*)

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
  wl;
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
  wl;
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
