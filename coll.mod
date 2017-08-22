(* Coll - Concatenative language with lazy lists *)

(* Aspirations:
      Evaluated nested Structures
      Support print [xxx]
      array operations [[1 2 3] [4 5 6] +] generates [5 7 9]
      stack at exit becomes the output
      literate operation
      Reduce number of types
      Function definition
*)

(* Strings represented by Chars vs Structures

   Chars are used
    . for independent text strings in the implementation independent of the client program
    . as a representation of program text that has not been compiled yet.

    Structures are used
     . to contain both uncompiled strings and source text. Only '[', ']' are interpreted.
     . to contain compiled porgrams

    When a structure is compiled, it's top level strings are parsed into intrinsics,
    numbers and functions. Only the top level is compiled, nested structures remain
    uncompiled until the compiled top level triggers compilation of the top level of
    a nested structure.

   For example

     1 2 + 3 4 + * [this substring]
     ^------------^^^------------^^
         |         |       |      +-- End of (sub) structure
         |         |       +--------- Chars
         |         +----------------- (sub) structure
         +----------------------------Chars

     As this is not yet compiled, the whole thing represents a string which can be
     manipulated by string functions.

     After compilation it will look like this

     1 2 + 3 4 + * [this substring]
     ^ ^   ^ ^                      -- Numbers
         ^     ^ ^                  -- intrinsic operations
                   ^^^------------^^
                   |       |      +-- End of (sub) structure
                   |       +--------- Chars
                   +----------------- (sub) structure


   Compilation is also lazy: When executing (aka evaluating) a structure, strings
   are compiled only as they are encountered: the string is replaced by the
   sequence of intrinsics, numbers and functions that it compiles to.

   Hmm, that still needs a flag to distinguish compiled and uncompiled structures.

   OK, change of approach. Don't parse strings into structures at all.
   When encountering '[' in source, record the content to the next matching ']' as
   a string.

   When evaluation encounters a string, at that point compile.

 *)

MODULE coll;

IMPORT In, Out, Strings;

CONST
  ExecuteAtomPassedNilAtom              = 1;
  ExecuteAtomPassedUnrecognisedAtomKind = 2;




TYPE
  CharBuf   = POINTER TO ARRAY OF CHAR;

  Atom      = POINTER TO AtomDesc; AtomDesc = RECORD next: Atom END;

  Number    = POINTER TO RECORD (AtomDesc) n: INTEGER END; (* n is the numeric value *)
  Chars     = POINTER TO RECORD (AtomDesc) c: CharBuf END;
  Intrinsic = POINTER TO RECORD (AtomDesc) i: INTEGER END; (* i is the intrinsic operation index *)
  Structure = POINTER TO RECORD (AtomDesc) a: Atom    END; (* a is the first entry in the list *)

VAR
  Dictionary:    Structure;
  Stack:         Atom;      (* points to top of stack *)
  Instruction:   Atom;      (* points to next instruction to be executed *)
  Input:         Chars;
  Abort:         BOOLEAN;   (* terminate current interactive line *)
  Exit:          BOOLEAN;   (* exit interpreter *)
  IntrinsicName: ARRAY 10 OF CharBuf;


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
PROCEDURE wi (i: INTEGER);       BEGIN IF Break THEN wc(' ') END; Out.Int(i,1); wb   END wi;

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

PROCEDURE ^PutAtomSeq(a: Atom);

PROCEDURE PutAtom(a: Atom);
BEGIN
  WITH
    a: Number    DO wi(a.n)
  | a: Chars     DO wc('"'); ws(a.c^); wc('"')
  | a: Intrinsic DO ws("I-"); wnb; ws(IntrinsicName[a.i]^)
  | a: Structure DO ws("[");  wnb; PutAtomSeq(a.a); wnb; ws("]")
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
VAR n: Number; s: Chars; i: Intrinsic; q: Structure;
BEGIN
  WITH
    a: Number    DO NEW(n); n.next := NIL; n.n := a.n; RETURN n
  | a: Chars     DO NEW(s); s.next := NIL; s.c := a.c; RETURN s
  | a: Intrinsic DO NEW(i); i.next := NIL; i.i := a.i; RETURN i
  | a: Structure DO NEW(q); q.next := NIL; q.a := a.a; RETURN q
  ELSE
    Fail("Dup passed atom it is not coded to support.");
  END;
END DupAtom;

PROCEDURE Push(a: Atom);
BEGIN
  a := DupAtom(a);  a.next := Stack;  Stack := a
END Push;

PROCEDURE MakeString(c: ARRAY OF CHAR): Chars;
VAR s: Chars;
BEGIN
  NEW(s); s.next := NIL;
  NEW(s.c, Strings.Length(c)+1);  COPY(c, s.c^);
  RETURN s
END MakeString;

PROCEDURE MakeIntrinsic(index: INTEGER): Intrinsic;
VAR i: Intrinsic;
BEGIN  NEW(i);  i.next := NIL;  i.i := index;  RETURN i
END MakeIntrinsic;

PROCEDURE MakeNumber(i: INTEGER): Number;
VAR n: Number;
BEGIN  NEW(n);  n.next := NIL;  n.n := i;  RETURN n
END MakeNumber;


(* ------------------------------ Dictionary ------------------------------ *)

PROCEDURE AddLookup(k: Atom; p: Atom);
VAR l: Structure;
BEGIN
  IF k IS Structure THEN k := k(Structure).a END;
  k := DupAtom(k);
  IF p IS Structure THEN k.next := p(Structure).a ELSE k.next := DupAtom(p) END;
  NEW(l); l.a := k;
  l.next := Dictionary;  Dictionary := l;

  (* Debugging, add names of intrinsics to IntrinsicName array. *)
  IF  (p IS Intrinsic)  &  (k IS Chars)  THEN
    IntrinsicName[p(Intrinsic).i] := k(Chars).c
  END;
  ws("Add loookup, key '"); wnb; PutAtom(k); wnb; ws("', loopup:"); PutAtom(p); wl
END AddLookup;

PROCEDURE MatchString(VAR source: ARRAY OF CHAR; offset, length: INTEGER; str: Chars): BOOLEAN;
VAR i: INTEGER;
BEGIN
  IF LEN(str.c^) # length+1 THEN RETURN FALSE END;
  i := 0;
  WHILE  (i < length)  &  (str.c^[i] = source[offset+i]) DO INC(i) END;
  RETURN i = length
END MatchString;

PROCEDURE Lookup(VAR source: ARRAY OF CHAR; offset, length: INTEGER): Atom;
VAR  l, p: Structure;  n: Number;
BEGIN
  l := Dictionary;
  WHILE l # NIL DO
    IF MatchString(source, offset, length, l.a(Chars)) THEN
      (* wsl("returning dictionary entry."); *)
      (* Token found in dictionary at l *)
      (* ws("Dictionary entry contains"); PutAtom(l); *)
      IF l.a.next.next = NIL THEN  (* TODO is there a difference between op and prog(op)? *)
        (* wsl("Treating as single item."); *)
        RETURN DupAtom(l.a.next)
      ELSE
        (* wsl("Treating as program."); *)
        NEW(p);  p.next := NIL;  p.a := l.a.next;  RETURN p
      END
    END;
    IF l.next = NIL THEN l := NIL ELSE l := l.next(Structure) END
  END;
  RETURN NIL
END Lookup;


(* ------------------------------ Intrinsics ------------------------------ *)

PROCEDURE ^ExecuteInstructions(a: Atom);

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
  result := Stack(Number).n; Stack := Stack.next; RETURN result
END PopNum;

PROCEDURE Functions;
VAR a: Atom;
BEGIN a := Dictionary;
  WHILE a # NIL DO
    WITH a: Structure DO PutAtom(a.a); wl
    ELSE ws("Unexpected atom in dictionary:"); PutAtom(a)
    END;
    a := a.next
  END
END Functions;

PROCEDURE PopAtom(): Atom;
VAR a: Atom;
BEGIN a := Stack; Stack := Stack.next; RETURN a
END PopAtom;

PROCEDURE DoTopOfStack;
VAR a: Atom;
BEGIN
  IF Stack IS Structure THEN
    a := PopAtom();
    ExecuteInstructions(a(Structure).a)
  END
END DoTopOfStack;

PROCEDURE ExecuteIntrinsic(i: INTEGER);
BEGIN
  CASE i OF
    0: Exit := TRUE; Abort := TRUE;
  | 1: wsl("Huh?")
  | 2: IF CheckStack(1) THEN Push(Stack)                                            END (* dup *)
  | 3: IF CheckStack(1) THEN Stack := Stack.next                                    END (* drop *)
  | 4: IF CheckStack(1) THEN PutAtom(Stack); Stack := Stack.next                    END (* put *)
  | 5: IF CheckStack(2) THEN Push(MakeNumber(PopNum()+PopNum()))                    END (* + *)
  | 6: IF CheckStack(2) THEN AddLookup(Stack, Stack.next); Stack := Stack.next.next END (* fn *)
  | 7: Functions
  | 8: IF CheckStack(1) THEN DoTopOfStack                                           END (* do *)
  ELSE wlc; ws("ExecuteIntrinsic"); wi(i); wsl("unknown.");
  END
END ExecuteIntrinsic;


(* ------------------------------ Execution ------------------------------- *)

PROCEDURE ^Compile(q: Structure): Atom;
PROCEDURE ^ParseStructure(VAR source: ARRAY OF CHAR; VAR i: INTEGER): Structure;

PROCEDURE ExecuteAtom(a: Atom);
VAR i: INTEGER;
BEGIN
  ASSERT(a # NIL, ExecuteAtomPassedNilAtom);
  WITH
    a: Number    DO Push(a)
  | a: Chars    DO i := 0; ExecuteInstructions(Compile(ParseStructure(a(Chars).c^, i)));
  | a: Structure DO Push(a)
  | a: Intrinsic DO ExecuteIntrinsic(a.i)
  ELSE
    Fail("ExecuteAtom passed unrecognised kind of atom.");
  END;
END ExecuteAtom;

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


(* ------------------------------- Parsing -------------------------------- *)

PROCEDURE CopySubstring(VAR source: ARRAY OF CHAR; offset, length: INTEGER): CharBuf;
VAR i: INTEGER; target: CharBuf;
BEGIN
  NEW(target, length+1);
  i := 0; WHILE (i<length) DO target[i] := source[offset+i]; INC(i) END;
  target[length] := 0X;
  RETURN target
END CopySubstring;

PROCEDURE ParseStructure(VAR source: ARRAY OF CHAR; VAR i: INTEGER): Structure;
(* Starting at index i, returns a list of strings and nested Structures *)
VAR f, a: Atom;  s: Chars;  q: Structure;  j: INTEGER;
BEGIN
  NEW(f);  f.next := NIL;  a := f; (* Dummy first atom with next var for real content *)
  WHILE  (i < LEN(source))  &  (source[i] # 0X)  &  (source[i] # ']')  DO
    (* Handle a string, if any *)
    j := i;
    WHILE  (j < LEN(source))  &  (source[j] # 0X)
        &  (source[j] # '[')  &  (source[j] # ']')  DO INC(j) END;
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
VAR  l, p: Structure;  n: Number;  a: Atom;
BEGIN
  Assert(length > 0, "ParseAtom passed empty string.");

  a := Lookup(source, offset, length);
  IF a # NIL THEN RETURN a END;

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


(* ----------------------- Compiler and interpreter ----------------------- *)

(* Compile
   Takes a character buffer and parses into
     -  numbers
     -  intrinsics
     -  function calls
     -  nested structures (which are not compiled - they remain as characters)
*)

PROCEDURE Compile(q: Structure): Atom;
VAR  f, a, t: Atom;
BEGIN
  a := q.a;
  ws("Compile: ");
  NEW(f); f.next := NIL; t := f;
  WHILE  (a # NIL)  &  (t # NIL)  DO
    wc('<'); PutAtom(a); wc('>');
    WITH
      a: Chars    DO  t.next := ParseProgram(a.c^); IF t.next # NIL THEN t := t.next END;
    | a: Structure DO  t.next := DupAtom(a);         t := t.next
    ELSE
      Fail("Structure contains atom that is neither string nor Structure.")
    END;
    a := a.next
  END;
  wl;
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

BEGIN Out.String("coll."); Out.Ln;
  Abort      := FALSE;
  Exit       := FALSE;
  Break      := FALSE;
  Dictionary := NIL;
  Stack      := NIL;
  AddLookup(MakeString("q"),         MakeIntrinsic(0));
  AddLookup(MakeString("huh?"),      MakeIntrinsic(1));
  AddLookup(MakeString("dup"),       MakeIntrinsic(2));
  AddLookup(MakeString("drop"),      MakeIntrinsic(3));
  AddLookup(MakeString("put"),       MakeIntrinsic(4));
  AddLookup(MakeString("+"),         MakeIntrinsic(5));
  AddLookup(MakeString("fn"),        MakeIntrinsic(6));
  AddLookup(MakeString("functions"), MakeIntrinsic(7));
  AddLookup(MakeString("do"),        MakeIntrinsic(8));
  Interpreter;
END coll.
