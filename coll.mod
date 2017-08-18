MODULE cob;

IMPORT In, Out, Strings;

CONST
  ExecuteAtomPassedNilAtom              = 1;
  ExecuteAtomPassedUnrecognisedAtomKind = 2;


TYPE
  Atom      = POINTER TO AtomDesc;      AtomDesc      = RECORD END;
  Number    = POINTER TO NumberDesc;    NumberDesc    = RECORD (AtomDesc)     n: INTEGER                  END;
  String    = POINTER TO StringDesc;    StringDesc    = RECORD (AtomDesc)     s: POINTER TO ARRAY OF CHAR END;
  Function  = POINTER TO FunctionDesc;  FunctionDesc  = RECORD (AtomDesc)                                 END;
  Quotation = POINTER TO QuotationDesc; QuotationDesc = RECORD (FunctionDesc) a: POINTER TO ARRAY OF Atom END;
  Intrinsic = POINTER TO IntrinsicDesc; IntrinsicDesc = RECORD (FunctionDesc) i: INTEGER                  END;

  Lookup = POINTER TO LookupDesc;
  LookupDesc = RECORD
    k: POINTER TO ARRAY OF CHAR;
    a: Atom;
    n: Lookup (* Next *)
  END;

  Stream = POINTER TO StreamDesc;
  StreamDesc = RECORD
    s: POINTER TO ARRAY OF CHAR;  (* String being parsed *)
    i: INTEGER;                   (* Current index *)
    l: INTEGER;                   (* Length up to which to read *)
  END;

VAR
  Dictionary: Lookup;
  Falsehood:  BOOLEAN;   (* Unwanted tricjk needed to allow ASSERT to compile. *)
  Missing:    Intrinsic; (* Called when lookup fails *)
  Stack: RECORD
    atoms: ARRAY 100 OF Atom;
    top: INTEGER;
  END;
  InputStream: Stream;

PROCEDURE Push(a: Atom);
BEGIN  Stack.atoms[Stack.top] := a;  INC(Stack.top)
END Push;

PROCEDURE AddLookup(k: ARRAY OF CHAR; a: Atom);
VAR l: Lookup;
BEGIN
  NEW(l);
  NEW(l.k, Strings.Length(k)+1);  COPY(k, l.k^);
  l.a := a;
  l.n := Dictionary;  Dictionary := l;
END AddLookup;

PROCEDURE MakeExit;
VAR i: Intrinsic;
BEGIN NEW(i);  i.i := 0;  AddLookup("exit", i);
END MakeExit;

PROCEDURE MakeIntrinsics;
BEGIN
  MakeExit;
END MakeIntrinsics;

PROCEDURE ExecuteIntrinsic(i: INTEGER): BOOLEAN;
BEGIN
  CASE i OF
    0: RETURN TRUE;
  | 1: Out.String("?"); Out.Ln; RETURN FALSE;
    ELSE
  END;
  RETURN FALSE;
END ExecuteIntrinsic;

PROCEDURE ^ExecuteAtom(a: Atom): BOOLEAN;
PROCEDURE ExecuteQuotation(VAR a: ARRAY OF Atom): BOOLEAN;
VAR i: INTEGER;
BEGIN
  i := 0;
  WHILE i < LEN(a) DO
    IF ExecuteAtom(a[i]) THEN RETURN TRUE END;
    INC(i)
  END;
  RETURN FALSE;
END ExecuteQuotation;

PROCEDURE ExecuteAtom(a: Atom): BOOLEAN;
BEGIN
  ASSERT(a # NIL, ExecuteAtomPassedNilAtom);
  WITH
    a: Number    DO Push(a);
  | a: String    DO Push(a);
  | a: Quotation DO RETURN ExecuteQuotation(a.a^)
  | a: Intrinsic DO RETURN ExecuteIntrinsic(a.i)
  ELSE
    ASSERT(Falsehood, ExecuteAtomPassedUnrecognisedAtomKind);
  END;
  RETURN TRUE;
END ExecuteAtom;

PROCEDURE IsSpecialChar(ch: CHAR): BOOLEAN;
BEGIN
  RETURN (ch = ' ')
      OR (ch = '[')
      OR (ch = ']')
      OR (ch = ':');
END IsSpecialChar;

PROCEDURE LookupWord(l: Lookup; VAR w: ARRAY OF CHAR): Atom;
BEGIN
  WHILE (l # NIL)  &  (l.k^ # w) DO l := l.n END;
  IF l = NIL THEN RETURN Missing ELSE RETURN l.a END;
END LookupWord;

PROCEDURE ParseWord(s: Stream; VAR w: ARRAY OF CHAR);
BEGIN
END ParseWord;

PROCEDURE ParseString(s: Stream; n: INTEGER);
BEGIN
END ParseString;

PROCEDURE Parse(s: Stream): Atom;
VAR word: ARRAY 100 OF CHAR; j: INTEGER;
BEGIN
  WHILE (s.i < s.l)  &  (s.s.s[s.i] = ' ') DO INC(s.i) END;
  j := 0;
  WHILE (s.i < s.l)  &  ~IsSpecialChar(s.s.s[s.i]) DO word[j] := s.s.s[s.i]; INC(s.i); INC(j) END;
  word[j] := 0X;
  RETURN LookupWord(Dictionary, word);
END Parse;

PROCEDURE Interpret(s: String): BOOLEAN;  (* Returns TRUE when exit requested *)
VAR stream: Stream; a: Atom;
BEGIN
  NEW(stream);
  stream.s := s;
  stream.i := 0;
  stream.l := Strings.Length(s.s^);
  WHILE stream.i < stream.l DO IF ExecuteAtom(Parse(stream)) THEN RETURN TRUE END END;
  RETURN FALSE;
END Interpret;

PROCEDURE Interpreter;
VAR s: String;
BEGIN
  NEW(s);  NEW(s.s, 300);  (* Input line buffer *)
  REPEAT
    Out.String("      : ");
    In.Line(s.s^);
  UNTIL Interpret(s)
END Interpreter;

BEGIN Out.String("Cob."); Out.Ln;
  Dictionary := NIL;
  Falsehood  := FALSE;
  Stack.top  := 0;
  NEW(Missing); Missing.i := 1;
  MakeIntrinsics;
  Interpreter;
END cob.
