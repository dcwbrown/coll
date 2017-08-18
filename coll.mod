MODULE cob;

IMPORT In, Out, Strings;

CONST
  ExecuteAtomPassedNilAtom              = 1;
  ExecuteAtomPassedUnrecognisedAtomKind = 2;


(*
TODO
Add next fild to atomdesc and use it to link
  atoms on the stak
  atoms in a quotation

Try making quotation execution lazy. Whenever we run out of code to execte and
the top of stack is a quotation, evaluate it.

Make get next quotation entry a function allowing a quotation to be implemented
as code, as in APL's iota. NextAtom takes a quotation and actually removes the
first atom from it by pointing the quotations atom pointer at the next atom.
(Use dup to take a copy that points at the original first entry, stopping the
  quotation getting garbage collected.)
When getting a quotation from a lookup, create a new quotation so that the original
one doesn't lose its content.
Or, maybe have an intermediate level type atom list which points at the first atom
and is copied from the quotation.
*)

TYPE

  Chars     = POINTER TO ARRAY OF CHAR;
  Atom      = POINTER TO AtomDesc;      AtomDesc      = RECORD next: Atom END;
  Lookup    = POINTER TO LookupDesc;    LookupDesc    = RECORD (AtomDesc) k: Chars; a: Atom END;
  Number    = POINTER TO NumberDesc;    NumberDesc    = RECORD (AtomDesc) n: INTEGER        END;
  String    = POINTER TO StringDesc;    StringDesc    = RECORD (AtomDesc) s: Chars          END;
  Intrinsic = POINTER TO IntrinsicDesc; IntrinsicDesc = RECORD (AtomDesc) i: INTEGER        END;
  Quotation = POINTER TO QuotationDesc; QuotationDesc = RECORD (AtomDesc) a: Atom           END;
  Operation = POINTER TO OperationDesc; OperationDesc = RECORD (AtomDesc) l: Lookup         END;

(* The next pointer of a lookup links dictionary entries
   The next pointer of Operation or String or Number links to the next in a quotaton or onm the stack
   The next pointer of an intrinsic is never used
*)
  Stream = RECORD
    s: Chars;    (* String being parsed *)
    i: INTEGER;  (* Current index *)
    l: INTEGER;  (* Length up to which to read *)
  END;

VAR
  Dictionary:  Lookup;
  Falsehood:   BOOLEAN;   (* Unwanted trick needed to allow ASSERT to compile. *)
  Stack:       Atom;      (* points to top of stack *)
  InputStream: Stream;
  Break:       BOOLEAN;
  SOL:         BOOLEAN;  (* At start of line *)

PROCEDURE wb;                    BEGIN Break := TRUE; SOL := FALSE                        END wb;
PROCEDURE wnb;                   BEGIN Break := FALSE                                     END wnb;
PROCEDURE ws (s: ARRAY OF CHAR); BEGIN IF Break THEN Out.Char(' ') END; Out.String(s); wb END ws;
PROCEDURE wl;                    BEGIN Out.Ln; wnb; SOL := TRUE                           END wl;
PROCEDURE wcl;                   BEGIN IF ~SOL THEN wl END                                END wcl;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl                                          END wsl;
PROCEDURE wi (i: INTEGER);       BEGIN IF Break THEN Out.Char(' ') END; Out.Int(i,1); wb  END wi;

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN wsl(msg); HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN ws("Assertion failure:"); Fail(msg) END
END Assert;

PROCEDURE CheckAtom(a: Atom);
BEGIN
  IF a # NIL THEN
    WITH
      a: Lookup    DO Assert((a.a IS Number) OR (a.a IS String) OR (a.a IS Operation), "Lookup references wrong type of atom.")
    | a: Number    DO
    | a: String    DO
    | a: Intrinsic DO Assert(a.next = NIL, "Intrinsic with non-NILL next.")
    | a: Quotation DO
    | a: Operation DO
    ELSE Assert(FALSE, "Unrecognised atom type.")
    END
  END
END CheckAtom;

PROCEDURE InitStream(VAR stream: Stream; string: Chars);
BEGIN
  stream.s := string;
  stream.i := 0;
  stream.l := Strings.Length(string^)
END InitStream;


PROCEDURE ^PutQuotation(q: Quotation);

PROCEDURE Put(a: Atom);
BEGIN
  WITH
    a: Number    DO wi(a.n)
  | a: String    DO ws(a.s^)
  | a: Quotation DO ws("["); wnb; PutQuotation(a); wnb; ws("]")
  | a: Operation DO ws(a.l.k^)
  | a: Intrinsic DO ws ("intrinsic-"); wnb; wi(a.i)
  ELSE              ws("**unrecognised**")
  END;
END Put;

PROCEDURE DuplicateAtom(a: Atom): Atom;
VAR n: Number; s: String; q: Quotation;
BEGIN
  WITH
    a: Number    DO NEW(n); n.next := NIL; n.n := a.n; RETURN n
  | a: String    DO NEW(s); s.next := NIL; s.s := a.s; RETURN s
  | a: Quotation DO NEW(q); q.next := NIL; q.a := a.a; RETURN q
  ELSE Fail("Internal error, DuplicateAtom passed unexpected atom type.")
  END
END DuplicateAtom;

PROCEDURE PutQuotation(q: Quotation);
VAR a: Atom;
BEGIN  a := q.a; WHILE a # NIL DO Put(a); a := a.next END;
END PutQuotation;

PROCEDURE Push(a: Atom);
BEGIN  a := DuplicateAtom(a);  a.next := Stack;  Stack := a
END Push;

PROCEDURE AddLookup(k: ARRAY OF CHAR; a: Atom);
VAR l: Lookup;
BEGIN
  NEW(l);
  NEW(l.k, Strings.Length(k)+1);  COPY(k, l.k^);
  l.a := a;
  l.next := Dictionary;  Dictionary := l;
END AddLookup;

PROCEDURE MakeIntrinsic(name: ARRAY OF CHAR; index: INTEGER);
VAR i: Intrinsic;
BEGIN  NEW(i);  i.i := index;  AddLookup(name, i)
END MakeIntrinsic;

PROCEDURE ExecuteIntrinsic(i: INTEGER): BOOLEAN;
BEGIN
  CASE i OF
    0: RETURN TRUE;                                                            (* Exit *)
  | 1: Out.String("huh?"); Out.Ln                                              (* huh? *)
  | 2: Assert(Stack # NIL, "Stack empty.");  Push(Stack)                       (* dup  *)
  | 3: Assert(Stack # NIL, "Stack empty.");  Stack := Stack.next               (* drop *)
  | 4: Assert(Stack # NIL, "Stack empty.");  Put(Stack); Stack := Stack.next   (* put  *)
    ELSE wcl; ws("ExecuteIntrinsic"); wi(i); wsl("unknown.");
  END;
  RETURN FALSE;
END ExecuteIntrinsic;

PROCEDURE ^ExecuteAtom(a: Atom): BOOLEAN;

PROCEDURE ExecuteQuotation(q: Quotation): BOOLEAN;
VAR a: Atom;
BEGIN
  a := q.a;
  WHILE a # NIL DO
    IF ExecuteAtom(a) THEN RETURN TRUE END;
    a := a.next
  END;
  RETURN FALSE;
END ExecuteQuotation;


PROCEDURE ExecuteOperation(a: Operation): BOOLEAN;
BEGIN RETURN ExecuteAtom(a.l.a)
END ExecuteOperation;

PROCEDURE ExecuteAtom(a: Atom): BOOLEAN;
  VAR at: Atom; b: BOOLEAN; l: Lookup;
BEGIN
  ASSERT(a # NIL, ExecuteAtomPassedNilAtom);
  WITH
    a: Number    DO Push(a); RETURN FALSE
  | a: String    DO Push(a); RETURN FALSE
  | a: Quotation DO Push(a); RETURN FALSE
  | a: Operation DO RETURN ExecuteOperation(a)
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

PROCEDURE LookupWord(l: Lookup; w: ARRAY OF CHAR): Lookup;
BEGIN  WHILE (l # NIL)  &  (l.k^ # w) DO l := l.next(Lookup) END;  RETURN l
END LookupWord;

PROCEDURE SkipBlanks(VAR s: Stream);
BEGIN WHILE  (s.i < s.l)  &  (s.s[s.i] = ' ')  DO INC(s.i) END;
END SkipBlanks;

PROCEDURE ParseWord(VAR s: Stream): Operation;
VAR  word: ARRAY 100 OF CHAR;  j: INTEGER;  l: Lookup;  o: Operation;
BEGIN
  j := 0;
  WHILE (s.i < s.l)  &  ~IsSpecialChar(s.s[s.i]) DO word[j] := s.s[s.i]; INC(s.i); INC(j) END;
  word[j] := 0X;
  l := LookupWord(Dictionary, word);
  IF l = NIL THEN l := LookupWord(Dictionary, "huh?") END;
  NEW(o);  o.l := l;
  RETURN o;
END ParseWord;

PROCEDURE ParseString(VAR s: Stream): String;
VAR  string: String;  i, j: INTEGER;
BEGIN NEW(string);
  i := s.i; WHILE  (s.i < s.l)  &  (s.s[s.i] # "'")  DO INC(s.i) END;
  NEW(string.s, s.i-i+1);
  j := 0;  WHILE i+j < s.i DO string.s[j] := s.s[i+j]; INC(j) END;
  string.s[j] := 0X;
  IF s.i < s.l THEN INC(s.i) END; (* Skip trailing qute *)
  RETURN string;
END ParseString;

PROCEDURE ParseQuotation(VAR s: Stream): Quotation;
VAR  word: ARRAY 100 OF CHAR;  i: INTEGER;  quotation: Quotation; a: Atom;
BEGIN
  (* wsl("Parse quotation."); *)
  NEW(quotation);  quotation.a := NIL;
  WHILE  (s.i < s.l)  &  (s.s[s.i] # ']')  DO
    a := NIL;
    CASE s.s[s.i] OF
      ' ': SkipBlanks(s)
    | "'": INC(s.i); a := ParseString(s)
    | "[": INC(s.i); a := ParseQuotation(s);
    ELSE   a := ParseWord(s)
    END;
    IF (a # NIL) THEN  a.next := quotation.a;  quotation.a := a;  END;
  END;
  IF  (s.i < s.l)  &  (s.s[s.i] = ']')  THEN INC(s.i) END;
  RETURN quotation;
END ParseQuotation;

PROCEDURE Parse(line: Chars): Quotation;
VAR s: Stream;
BEGIN  InitStream(s, line);  RETURN ParseQuotation(s);
END Parse;

PROCEDURE DumpQuotation(q: Quotation);
VAR a: Atom;
BEGIN
  a := q.a;
  ws("Parsed quotation:");
  WHILE a # NIL DO
    WITH
      a: Number    DO wi(a.n)
    | a: String    DO ws("'"); wnb; ws(a.s^); wnb; ws("'")
    | a: Quotation DO ws("quotation")
    | a: Operation DO ws("operation-"); wnb; ws(a.l.k^)
    | a: Intrinsic DO ws("intrinsic-"); wnb; wi(a.i)
    ELSE              ws("**unrecognised**")
    END;
    a := a.next;
  END;
  wl;
END DumpQuotation;

PROCEDURE Interpreter;
VAR line: Chars;  quotation: Quotation;
BEGIN
  NEW(line, 300);  (* Input line buffer *)
  REPEAT
    ws("      : "); wnb;
    In.Line(line^);
    quotation := Parse(line);
    DumpQuotation(quotation);
  UNTIL ExecuteQuotation(quotation);
END Interpreter;

BEGIN Out.String("Cob."); Out.Ln;
  Break      := FALSE;
  Dictionary := NIL;
  Falsehood  := FALSE;
  Stack      := NIL;
  MakeIntrinsic("exit", 0);
  MakeIntrinsic("huh?", 1);
  MakeIntrinsic("dup",  2);
  MakeIntrinsic("drop", 3);
  MakeIntrinsic("put",  4);
  Interpreter;
END cob.
