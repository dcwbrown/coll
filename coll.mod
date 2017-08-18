(* Aspirations:
      Evaluated nested Structures
      Support print [xxx]
      array operations [[1 2 3] [4 5 6] +] generates [5 7 9]
      stack at exit becomes the output
      literate operation
      Reduce number otf types
      Function definition
*)


MODULE cob;

IMPORT In, Out, Strings;

CONST
  ExecuteAtomPassedNilAtom              = 1;
  ExecuteAtomPassedUnrecognisedAtomKind = 2;




TYPE
  Chars     = POINTER TO ARRAY OF CHAR;

  Atom      = POINTER TO AtomDesc;      AtomDesc      = RECORD next: Atom END;

  Number    = POINTER TO NumberDesc;    NumberDesc    = RECORD (AtomDesc) n: INTEGER END; (* n is the numeric value *)
  String    = POINTER TO StringDesc;    StringDesc    = RECORD (AtomDesc) c: Chars   END;
  Intrinsic = POINTER TO IntrinsicDesc; IntrinsicDesc = RECORD (AtomDesc) i: INTEGER END; (* i is the intrinsic operation index *)
  List      = POINTER TO ListDesc;      ListDesc      = RECORD (AtomDesc) a: Atom    END; (* a is the first entry n te list *)

  Structure = POINTER TO StructureDesc; StructureDesc = RECORD (ListDesc) END;  (* a list of strings and nested structures *)
  Program   = POINTER TO ProgramDesc;   ProgramDesc   = RECORD (ListDesc) END;  (* a list of numbers, strings, intrinsics and nested structures or programs *)
  Lookup    = POINTER TO LookupDesc;    LookupDesc    = RECORD (ListDesc) END;  (* a string (key) followed by a number, a string, an intrinsic or a program *)

VAR
  Dictionary:  Lookup;
  Stack:       Atom;      (* points to top of stack *)
  Instruction: Atom;      (* points to next instruction to be executed *)
  Input:       String;
  Abort:       BOOLEAN;   (* terminate current interactive line *)
  Exit:        BOOLEAN;   (* exit interpreter *)


  Break:       BOOLEAN;
  SOL:         BOOLEAN;  (* At start of line *)

PROCEDURE wb;                    BEGIN Break := TRUE; SOL := FALSE                        END wb;
PROCEDURE wnb;                   BEGIN Break := FALSE                                     END wnb;
PROCEDURE wc (c: CHAR);          BEGIN Out.Char(c); wnb                                   END wc;
PROCEDURE ws (s: ARRAY OF CHAR); BEGIN IF Break THEN Out.Char(' ') END; Out.String(s); wb END ws;
PROCEDURE wl;                    BEGIN Out.Ln; wnb; SOL := TRUE                           END wl;
PROCEDURE wlc;                   BEGIN IF ~SOL THEN wl END                                END wlc;
PROCEDURE wsl(s: ARRAY OF CHAR); BEGIN ws(s); wl                                          END wsl;
PROCEDURE wi (i: INTEGER);       BEGIN IF Break THEN Out.Char(' ') END; Out.Int(i,1); wb  END wi;

PROCEDURE Fail(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Internal error:"); wsl(msg); HALT(99)
END Fail;

PROCEDURE Assert(truth: BOOLEAN; msg: ARRAY OF CHAR);
BEGIN IF ~truth THEN wlc; ws("Assertion failure:"); wsl(msg); HALT(99) END
END Assert;

PROCEDURE Error(msg: ARRAY OF CHAR);
BEGIN wlc; ws("Error:"); wsl(msg); Abort := TRUE
END Error;


PROCEDURE ^PutAtomSeq(a: Atom);

PROCEDURE PutAtom(a: Atom);
BEGIN
  WITH
    a: Number    DO wi(a.n)
  | a: String    DO ws(a.c^)
  | a: Intrinsic DO ws("I-"); wnb; wi(a.i)
  | a: Structure DO ws("Q["); wnb; PutAtomSeq(a.a); wnb; ws("]")
  | a: Program   DO ws("P["); wnb; PutAtomSeq(a.a); wnb; ws("]")
  | a: Lookup    DO ws("L["); wnb; PutAtomSeq(a.a); wnb; ws("]")
  | a: List      DO ws("?["); wnb; PutAtomSeq(a.a); wnb; ws("]")
  ELSE Fail("Put was passed an unrecognised atom.")
  END;
END PutAtom;

PROCEDURE PutAtomSeq(a: Atom);
BEGIN WHILE a # NIL DO PutAtom(a); a := a.next END
END PutAtomSeq;

PROCEDURE PutAtomStack(a: Atom);
BEGIN IF a # NIL THEN PutAtomStack(a.next); PutAtom(a) END
END PutAtomStack;


PROCEDURE DupAtom(a: Atom): Atom; (* Shallow copy *)
VAR n: Number; s: String; i: Intrinsic; q: Structure; p: Program;
BEGIN
  WITH
    a: Number    DO NEW(n); n.next := NIL; n.n := a.n; RETURN n
  | a: String    DO NEW(s); s.next := NIL; s.c := a.c; RETURN s
  | a: Intrinsic DO NEW(i); i.next := NIL; i.i := a.i; RETURN i
  | a: Structure DO NEW(q); q.next := NIL; q.a := a.a; RETURN q
  | a: Program   DO NEW(p); p.next := NIL; p.a := a.a; RETURN p
  ELSE
    Fail("Dup passed atom it is not coded to support.");
  END;
END DupAtom;

PROCEDURE Push(a: Atom);
BEGIN
  a := DupAtom(a);  a.next := Stack;  Stack := a
END Push;

PROCEDURE Pop;
BEGIN Stack := Stack.next
END Pop;

PROCEDURE MakeString(c: ARRAY OF CHAR): String;
VAR s: String;
BEGIN
  NEW(s); s.next := NIL;
  NEW(s.c, Strings.Length(c)+1);  COPY(c, s.c^);
  RETURN s
END MakeString;

PROCEDURE AddLookup(k: ARRAY OF CHAR; a: Atom);
VAR l: Lookup; s: String;
BEGIN
  s := MakeString(k); s.next := a;
  NEW(l); l.a := s;
  l.next := Dictionary;  Dictionary := l
END AddLookup;

PROCEDURE MakeIntrinsic(index: INTEGER): Intrinsic;
VAR i: Intrinsic;
BEGIN  NEW(i);  i.next := NIL;  i.i := index;  RETURN i
END MakeIntrinsic;

PROCEDURE MakeNumber(i: INTEGER): Number;
VAR n: Number;
BEGIN  NEW(n);  n.next := NIL;  n.n := i;  RETURN n
END MakeNumber;


(* ------------------------------ Intrinsics ------------------------------ *)

PROCEDURE CheckStack(n: INTEGER): BOOLEAN;
VAR s: Atom;
BEGIN s := Stack;
  WHILE n > 0 DO
    IF s = NIL THEN Error("Insufficient parameters on stack."); RETURN FALSE END;
    s := s.next; DEC(n)
  END;
  RETURN TRUE;
END CheckStack;

PROCEDURE PopNum(): INTEGER;
VAR result: INTEGER;
BEGIN
  IF Stack = NIL THEN Error("Number expected but stack empty."); RETURN 0 END;
  IF ~(Stack IS Number) THEN Error("Number expected."); RETURN 0 END;
  result := Stack(Number).n; Pop; RETURN result
END PopNum;

PROCEDURE ExecuteIntrinsic(i: INTEGER);
BEGIN
  CASE i OF
    0: Exit := TRUE; Abort := TRUE;
  | 1: wsl("Huh?")
  | 2: IF CheckStack(1) THEN Push(Stack)                         END (* dup *)
  | 3: IF CheckStack(1) THEN Pop                                 END (* drop *)
  | 4: IF CheckStack(1) THEN PutAtom(Stack); Pop                 END (* put *)
  | 5: IF CheckStack(2) THEN Push(MakeNumber(PopNum()+PopNum())) END (* + *)
  ELSE wlc; ws("ExecuteIntrinsic"); wi(i); wsl("unknown.");
  END
END ExecuteIntrinsic;


PROCEDURE ^ExecuteAtom(a: Atom);

PROCEDURE ExecuteInstructions(a: Atom);
VAR prevInstruction: Atom;
BEGIN
  prevInstruction := Instruction;  Instruction := a;
  wlc; ws("Execute instructions: "); PutAtomSeq(Instruction); wnb; wsl(".");
  WHILE  (Instruction # NIL)  &  ~Abort  DO
    ExecuteAtom(Instruction);  Instruction := Instruction.next
  END;
  Instruction := prevInstruction;
END ExecuteInstructions;

PROCEDURE ExecuteAtom(a: Atom);
BEGIN
  ASSERT(a # NIL, ExecuteAtomPassedNilAtom);
  WITH
    a: Number    DO Push(a)
  | a: String    DO Push(a)
  | a: Structure DO Push(a)
  | a: Intrinsic DO ExecuteIntrinsic(a.i)
  | a: Program   DO ExecuteInstructions(a.a);
  | a: Lookup    DO ExecuteInstructions(a.a.next);
  ELSE
    Fail("ExecuteAtom passed unrecognised kind of atom.");
  END;
END ExecuteAtom;


PROCEDURE CopySubstring(VAR source: ARRAY OF CHAR; offset, length: INTEGER): Chars;
VAR i: INTEGER; target: Chars;
BEGIN
  NEW(target, length+1);
  i := 0; WHILE (i<length) DO target[i] := source[offset+i]; INC(i) END;
  target[length] := 0X;
  RETURN target
END CopySubstring;

PROCEDURE ParseStructure(VAR source: ARRAY OF CHAR; VAR i: INTEGER): Structure;
(* Staring at index i, returns a list of strings and nested Structures *)
VAR f, a: Atom;  s: String;  q: Structure;  j: INTEGER;
BEGIN
  NEW(f);  f.next := NIL;  a := f; (* Dummy first atom with next var for real content *)
  WHILE  (i < LEN(source))  &  (source[i] # 0X)  &  (source[i] # ']')  DO
    (* Handle a string, if any *)
    j := i;
    WHILE  (j < LEN(source))   &  (source[j] # 0X)
        &  (source[j] # '[')   &  (source[j] # ']') DO INC(j) END;
    IF (j > i) THEN
      NEW(s);  s.next := NIL;  s.c := CopySubstring(source, i, j-i);
      a.next := s; a := s;
      i := j;
    END;
    (* Handle a nested Structure, if any *)
    IF  (i < LEN(source))  &  (source[i] = '[') THEN
      INC(i); a.next := ParseStructure(source, i); a := a.next;
      IF  (i < LEN(source))  &  (source[i] = ']') THEN INC(i) END;
    END
  END;
  NEW(q);  q.next := NIL;  q.a := f.next; RETURN q
END ParseStructure;


PROCEDURE MatchString(VAR source: ARRAY OF CHAR; offset, length: INTEGER; str: String): BOOLEAN;
VAR i: INTEGER;
BEGIN
  IF LEN(str.c^) # length+1 THEN RETURN FALSE END;
  i := 0;
  WHILE  (i < length)  &  (str.c^[i] = source[offset+i]) DO INC(i) END;
  RETURN i = length
END MatchString;

PROCEDURE ParseNumber(VAR source: ARRAY OF CHAR; offset, length: INTEGER): INTEGER;
VAR i, n: INTEGER;
BEGIN
  n := 0;  i := offset;
  WHILE i < offset+length DO
    Assert((source[i] >= '0')  &  (source[i] <= '9'), "Invalid character in number.");
    n := n*10 + ORD(source[i]) - ORD('0');
    INC(i)
  END;
  RETURN n
END ParseNumber;

PROCEDURE ParseAtom(VAR source: ARRAY OF CHAR; offset, length: INTEGER): Atom;
VAR  l: Atom;  p: Program;  n: Number;  dbg: Chars;
BEGIN

  dbg := CopySubstring(source, offset, length);
  wlc; ws("ParseAtom('"); wnb; ws(dbg^); wnb; ws("')");

  Assert(length > 0, "ParseAtom passed empty string.");
  l := Dictionary;
  WHILE l # NIL DO
    IF MatchString(source, offset, length, l(Lookup).a(String)) THEN
      wsl("returning dictionary entry.");
      (* Token found in dictionary at l *)
      ws("Dictionary entry contains"); PutAtom(l);
      IF l(Lookup).a.next.next = NIL THEN  (* TODO is there a difference between op and prog(op)? *)
        wsl("Treating as single item.");
        RETURN DupAtom(l(Lookup).a.next)
      ELSE
        wsl("Treating as program.");
        NEW(p);  p.next := NIL;  p.a := l(Lookup).a.next;  RETURN p
      END
    END;
    l := l.next
  END;

  IF  (source[offset] >= '0')  &  (source[offset] <= '9')  THEN
    NEW(n);  n.next := NIL;  n.n := ParseNumber(source, offset, length);
    ws("returning number"); wi(n.n); wnb; wsl(".");
    RETURN n
  END;

  wsl("unrecognised.");
  Error("Parse failed.");
  RETURN NIL
END ParseAtom;


PROCEDURE ParseProgram(VAR source: ARRAY OF CHAR): Atom;
VAR  f, a: Atom;  i, j: INTEGER;
BEGIN
  NEW(f);  f.next := NIL;  a := f; (* Dummy first atom with next var for real content *)
  i := 0;
  WHILE  (i < LEN(source))  &  (source[i] # 0X)  &  ~Abort  DO
    WHILE  (i < LEN(source))  &  (source[i] = ' ') DO INC(i) END;
    j := i;  WHILE  (j < LEN(source))  &  (source[j] # ' ')  &  (source[j] # 0X) DO INC(j) END;
    IF (j > i) THEN (* Determine what the string from i to j is *)
      a.next := ParseAtom(source, i, j-i);
      IF a.next # NIL THEN a := a.next END;
      i := j
    END
  END;
  RETURN f.next;
END ParseProgram;

PROCEDURE Compile(q: Structure): Atom;
VAR  f, a, t: Atom;
BEGIN
  a := q.a;
  NEW(f); f.next := NIL; t := f;
  WHILE a # NIL DO
    WITH
      a: String    DO  t.next := ParseProgram(a.c^); t := t.next
    | a: Structure DO  t.next := DupAtom(a);         t := t.next
    ELSE
      Fail("Structure contains atom that is neither string nor Structure.")
    END;
    a := a.next
  END;
  RETURN f.next
END Compile;

PROCEDURE Interpreter;
VAR line: ARRAY 300 OF CHAR;  i: INTEGER;
BEGIN
  REPEAT
    Abort := FALSE;  i := 0;
    ws("      : "); wnb;  In.Line(line);
    ExecuteInstructions(Compile(ParseStructure(line, i)));
    wlc; ws("Stack:");  PutAtomStack(Stack); wl;
  UNTIL Exit;
END Interpreter;

BEGIN Out.String("Cob."); Out.Ln;
  Abort      := FALSE;
  Exit       := FALSE;
  Break      := FALSE;
  Dictionary := NIL;
  Stack      := NIL;
  AddLookup("q",    MakeIntrinsic(0));
  AddLookup("huh?", MakeIntrinsic(1));
  AddLookup("dup",  MakeIntrinsic(2));
  AddLookup("drop", MakeIntrinsic(3));
  AddLookup("put",  MakeIntrinsic(4));
  AddLookup("+",    MakeIntrinsic(5));
  Interpreter;
END cob.
