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
  Abort: BOOLEAN;


(* ---------------------------- Console output ---------------------------- *)

  Break:       BOOLEAN;
  SOL:         BOOLEAN;  (* At start of line *)

PROCEDURE wb;                    BEGIN Break := TRUE; SOL := FALSE                   END wb;
PROCEDURE wnb;                   BEGIN Break := FALSE                                END wnb;
PROCEDURE wc(c: CHAR);           BEGIN Out.Char(c); wnb                              END wc;
PROCEDURE ws(s: ARRAY OF CHAR);  BEGIN IF Break THEN wc(' ') END; Out.String(s); wb  END ws;
PROCEDURE wl;                    BEGIN Out.Ln; wnb; SOL := TRUE                      END wl;
PROCEDURE wlc;                   BEGIN IF ~SOL THEN wl END                           END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl                                     END wsl;
PROCEDURE wi (i: LONGINT);       BEGIN IF Break THEN wc(' ') END; Out.Int(i,1); wb   END wi;

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


PROCEDURE Find*(key: CharBuf; a: Atom): Atom;
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
END Find;



PROCEDURE NewSuffix(key: CharBuf; offset: LONGINT; target: Atom): Prefix;
VAR i, l: LONGINT; p: Prefix;
BEGIN
  NEW(p); p.next := target; p.mismatch := NIL;
  IF key = NIL THEN l := 0 ELSE l := LEN(key^) - offset - 1 END;
  IF l > 0 THEN
    NEW(p.characters, l+1);
    FOR i := 0 TO l-1 DO p.characters[i] := key[i+offset] END;
    p.characters[l] := 0X
  ELSE
    p.characters := NIL
  END;
  RETURN p
END NewSuffix;


(*  Store methodology

    1) Advance through the key prepresentation while a Prefix record entirely
       matches the next part of the key.
    2) If reach a Prefix that partly matches the key, split the prefix into
       two.

    Now we have reached a point where an existing Prefix record and the new
    key are either both at the end, or they diverge.

    We need to handle these cases:

    Key       Store         Action
    ---       -----         ------
    empty     non-prefix    Key alreay present
    empty     empty-prefix  Key already present
    empty     prefix        Follow mismatch link looking for empty prefix
                            if found:  Key already present
                            not found: Add empty prefix referencing target
    nonempty  non-prefix    Create empty prefix and continue as below
    nonempty  empty-prefix  Add remaining key under mismatch
    nonempty  prefix
*)


PROCEDURE StoreInternal(key: CharBuf; offset: LONGINT; target: Atom; VAR a: Atom);
VAR kl, ml, pl: LONGINT; p, q: Prefix;
BEGIN
  kl := ContentLength(key) - offset;  p := NIL;  ml := 0;

  (* Advance over prefixes that fully match next part of key *)
  IF (kl > 0) & (a # NIL) & (a IS Prefix) THEN
    p := a(Prefix);  ml := MatchString(key^, offset, p.characters);

    (*
    ws("*1* kl"); wi(kl); ws("p.characters");
    IF p.characters = NIL THEN ws("<NIL>") ELSE ws(p.characters^) END;
    ws("ml"); wi(ml); wsl(".");
    *)

    (* Scan the mismatch list at this level as necessary *)
    IF (ml = 0) & (p.characters # NIL) & (p.mismatch # NIL) THEN
      StoreInternal(key, offset, target, p.mismatch(Atom));
      RETURN
    END;

    IF ml > 0 THEN
      pl := ContentLength(p.characters);
      IF ml < pl THEN(* Split Prefix node into two *)
        (*ws("Split"); wi(pl); ws("character prefix at"); wi(ml); wl;*)
        NEW(q); q.characters := MakeCharBuf(p.characters^, ml, pl-ml);
        p.characters := MakeCharBuf(p.characters^, 0, ml);
        q.mismatch := NIL; q.next := p.next;
        p.next := q;
      END;
      StoreInternal(key, offset+ml, target, a.next);
      RETURN
    END;

    Assert(ml = 0, "ml # 0");
  END;

  (* Should only reach here at end of matching part.
     By design we've reached the end of the key, or then end of a prefix match
  *)

  IF a = NIL THEN a := NewSuffix(key, offset, target); RETURN END;

  IF ~(a IS Prefix) THEN
    IF kl = 0 THEN
      a := target (* Replace target *)
    ELSE
      a := NewSuffix(NIL, 0, a);
      a(Prefix).mismatch := NewSuffix(key, offset, target);
    END;
    RETURN
  END;

  (* By design a is a Prefix with zero matching length *)

  Assert(ml=0, "ml#0");  Assert(a IS Prefix, "a not Prefix");
  IF kl = 0 THEN
    p := a(Prefix);
    IF p.characters = NIL THEN
      p.next := target
    ELSE
      NEW(q); q.characters := NIL; q.next := target;
      q.mismatch := p.mismatch; p.mismatch := q;
    END;
    RETURN
  END;

  p := a(Prefix);
  (*
  IF (p # NIL) & (p.mismatch # NIL) THEN
    ws("p.characters"); IF p.characters = NIL THEN ws("<NIL>") ELSE ws(p.characters^) END;
    wnb; ws(", p.mismatch.characters");
    IF p.mismatch(Prefix).characters = NIL THEN ws("<NIL>") ELSE ws(p.mismatch(Prefix).characters^) END;
    wl;
  END;
  *)
  q := NewSuffix(key, offset, target);
  q.mismatch := p.mismatch;
  p.mismatch := q
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
VAR i: LONGINT;
BEGIN
  ws("'"); wnb; IF p.characters # NIL THEN Out.String(p.characters^); wnb END;
  ws("' "); wnb;
  IF    p.next = NIL     THEN Out.Ln
  ELSIF p.next IS Prefix THEN DumpPrefixTree(p.next(Prefix), depth + ContentLength(p.characters)+3)
  ELSE  Out.String(" -> "); Out.Int(p.next(Number).n,1); Out.Ln
  END;
  IF p.mismatch # NIL THEN
    FOR i := 0 TO depth-1 DO Out.Char(' ') END;
    DumpPrefixTree(p.mismatch(Prefix), depth)
  END
END DumpPrefixTree;


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

BEGIN
  Abort := FALSE;  Break := TRUE;  SOL := TRUE;
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
END PrefixMap.
