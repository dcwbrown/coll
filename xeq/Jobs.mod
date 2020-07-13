MODULE Jobs;  IMPORT w, Codespace, Codegen, SYSTEM;

(* Vague todos:
   o  Define prefix, postfix and dyadic functions
   o  Parse from definitions
   o  Allow over (reduce) implementation to use dyadic functions
   o  Compile. Maybe an IsSingleton fn?
   o  Named value and function definition and invocation
   o  Nested language (and eventually, formatted output)
   o  Distinguish integers and characters just enough
   o  Support partial dyadic operators - where one arg is preset
   o  Less reduction to integer maybe
*)

CONST
  (* Object kinds *)
  Nobj      = 0;    (* None                                *)

  (* Scalar/linked list types *)
  Integer   = 1;    (* a singleton integer value           *)

  (* Parse operator types *)
  Prefix    = 2;
  Infix     = 3;
  Postfix   = 4;

  (* Other steppables needing a stepper object *)
  Iota      = 5;    (* a vector of 0 up to a limit         *)
  Repeat    = 6;    (* repeats a source multiple times     *)

  Stepper   = 7;    (* Steps through algorithmic sequences *)

  (* Operators not needing a stepper object *)
  Negate    = 10;   (* monadic operators                   *)
  Not       = 11;
  Square    = 12;
  Identity  = 13;
  Add       = 14;   (* dyadic operators                    *)
  Subtract  = 15;
  Multiply  = 16;
  Divide    = 17;
  Modulo    = 18;
  And       = 19;
  Or        = 20;
  Equal     = 21;   (* returns 0s and 1s                   *)
  Factorial = 22;

  (* Reduction operators *)
  Match     = 23;   (* walk match tree                     *)
  Merge     = 24;   (* merge into match tree               *)
  Over      = 25;   (* Applicator                          *)

  (* Tokens *)
  Open      = 27;   (* Parse of '(' *)
  Close     = 28;   (* Parse of ')' *)
  (* TreeRoot  = 28; *)   (* Parse of 't' *)

  ObjLimit  = 29;


  (*  ============ object ============      =========== stepper ============
      Kind       p       q       i          p           q          i
      --------   -----   -----   -----      ---------   --------   ---------
      Integer    /       alt     value      first       curr int   curr val
      Iota       parm    /       max        Iota        Iota       curr val
      Repeat     parm1   parm2   iterno     Repeat      Repeat     curr val
      Negate     parm    /       val
      Not        parm    /       val
      Square     parm    /       val
      Add        parm1   parm2   val
      Subtract   parm1   parm2   val
      Multiply   parm1   parm2   val
      Divide     parm1   parm2   val
      Over       parm    /       val
      Stepper    <See cols to right>
  *)

  (*  Reset   - reloads p.i with first value
      More    - returns whether there are more values available
      Advance - steps p.i to the next  value
  *)

TYPE
  Int   = SYSTEM.INT64;
  Ptr   = POINTER TO Obj;
  Obj   = RECORD  kind, i: Int;  n, p, q: Ptr  END;
  OpDef = RECORD  prefix, dyadic, priority: Int  END;

VAR
  Ops:  ARRAY 128 OF OpDef;
  Tree: Ptr;

(* ------------------------------------------------------------------------ *)

PROCEDURE Fail(s: ARRAY OF CHAR);                   BEGIN w.Fail(s)      END Fail;
PROCEDURE Assert(t: BOOLEAN; s: ARRAY [1] OF CHAR); BEGIN w.Assert(t, s) END Assert;

(* ------------------------------------------------------------------------ *)

PROCEDURE wkind(k: Int);
BEGIN CASE k OF
|Nobj:      w.s("Nobj")
|Integer:   w.s("Integer")
|Prefix:    w.s("Prefix")
|Infix:     w.s("Infix")
|Postfix:   w.s("Postfix")
|Iota:      w.s("Iota")
|Repeat:    w.s("Repeat")
|Negate:    w.s("Negate")
|Not:       w.s("Not")
|Square:    w.s("Square")
|Identity:  w.s("Identity")
|Add:       w.s("Add")
|Subtract:  w.s("Subtract")
|Multiply:  w.s("Multiply")
|Divide:    w.s("Divide")
|Modulo:    w.s("Modulo")
|And:       w.s("And")
|Or:        w.s("Or")
|Equal:     w.s("Equal")
|Factorial: w.s("Factorial")
|Match:     w.s("Match")
|Merge:     w.s("Merge")
|Over:      w.s("Over")
|Stepper:   w.s("Stepper")
|Open:      w.s("Open")
|Close:     w.s("Close")
(* |TreeRoot:  w.s("TreeRoot") *)
|ObjLimit:  w.s("ObjLimit")
ELSE        w.s("Unknown-kind "); w.i(k)
END END wkind;


(* ------------------------------------------------------------------------ *)


PROCEDURE EvaluateFactorial(i: Int): Int;
VAR result: Int;
BEGIN
  Assert(i >= 0, "Factorial not defined for negative integers");
  result := 1;
  WHILE i > 1 DO result := result * i;  DEC(i) END;
RETURN result END EvaluateFactorial;

(* ------------------------------------------------------------------------ *)

PROCEDURE NewObj(kind: Int;  p: Ptr;  i: Int): Ptr;
VAR obj: Ptr;
BEGIN Assert(kind # Nobj, "NewObj passed object kind Nobj.");
  NEW(obj);
  obj.kind := kind;  obj.p := p;  obj.i  := i;
RETURN obj END NewObj;

PROCEDURE BoolVal(b: BOOLEAN): Int;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE^ Reset(VAR p: Ptr);
PROCEDURE^ Advance(p: Ptr);
PROCEDURE^ More(p: Ptr): BOOLEAN;

PROCEDURE MatchPattern(VAR p, k: Ptr);  (* pattern, key *)
BEGIN
  Assert(p.kind = Stepper, "MatchPattern expects pattern to be stepper.");
  Assert(k.kind = Stepper, "MatchPattern expects key to be stepper.");
  LOOP
    WHILE (p.q.kind = Integer) & (k.i # p.i) & (p.q.q # NIL) DO
      p.q := p.q.q;  p.i := p.q.i;
    END;
    IF (k.i = p.i) & More(k) & More(p) THEN
      Advance(k); Advance(p)
    ELSE
      EXIT
    END
  END
END MatchPattern;

PROCEDURE EvaluateMerge(VAR r: Ptr): Int;
VAR p, k: Ptr;  (* Pattern and Key *)
BEGIN  p := r.p;  k := r.q;
  MatchPattern(p, k);
  Assert(p.kind = Stepper, "Merge expects pattern to be stepper.");
  Assert(k.kind = Stepper, "Merge expects key to be stepper.");
  IF p.i = k.i THEN  (* At least partial match *)
    IF More(k) THEN
      Assert(p.q.kind = Integer, "Cannot merge key to non-integer.");
      Assert(k.q.kind = Integer, "Cannot merge key from non-integer.");
      Assert(p.q.n = NIL,        "Internal failure, attempt to merge to middle of pattern.");
      p.q.n := k.q.n;
      RETURN 1  (* Success *)
    ELSE
      (* IF ~More(p) THEN w.sl("EvaluateMerge warning: Pattern incomplete at end of key.") END; *)
      RETURN 0  (* No action taken *)
    END
  ELSE  (* Found first mismatch *)
    (* Insert current pos in key as alternate in current pos of pattern *)
    Assert(p.q.kind = Integer, "Merge expects current pattern to be integer.");
    Assert(k.q.kind = Integer, "Merge expects current key to be integer.");
    Assert(p.q.q = NIL, "Internal failure, merge has not reached last existing alternative.");
    p.q.q := k.q;
    RETURN 1
  END
END EvaluateMerge;

PROCEDURE EvaluateOver(p: Ptr): Int;  (* p -> Over, p.p -> Stepper *)
VAR i: Int;
BEGIN
  Assert(p.kind = Over,      "Expected p -> Over in EvaluateOver.");
  Assert(p.p.kind = Stepper, "Expected p.p -> Stepper in EvaluateOver.");
  IF p.p.kind # Stepper THEN w.s("Expected stepper in EvaluateOver, got "); wkind(p.kind); w.sl(".") END;
  CASE p.q.kind OF
  |Add:      i := p.p.i;  WHILE More(p.p) DO Advance(p.p);  i := i  +  p.p.i END
  |Subtract: i := p.p.i;  WHILE More(p.p) DO Advance(p.p);  i := i  -  p.p.i END
  |Multiply: i := p.p.i;  WHILE More(p.p) DO Advance(p.p);  i := i  *  p.p.i END
  |Divide:   i := p.p.i;  WHILE More(p.p) DO Advance(p.p);  i := i DIV p.p.i END
  |And:      WHILE (p.p.i # 0) & More(p.p) DO Advance(p.p) END;  i := BoolVal(p.p.i # 0)
  |Or:       WHILE (p.p.i = 0) & More(p.p) DO Advance(p.p) END;  i := BoolVal(p.p.i # 0)
  ELSE       w.Fail("Unsupported over operator.")
  END;
RETURN i END EvaluateOver;

PROCEDURE Evaluate(p: Ptr): Int;
BEGIN CASE p.kind OF
|Stepper:    Fail("Evaluate passed Stepper.");
|Negate:     RETURN -p.p.i
|Identity:   RETURN p.p.i
|Factorial:  RETURN EvaluateFactorial(p.p.i)
|Not:        RETURN BoolVal(p.p.i = 0)
|Square:     RETURN p.p.i  *  p.p.i
|Add:        RETURN p.p.i  +  p.q.i
|Subtract:   RETURN p.p.i  -  p.q.i
|Multiply:   RETURN p.p.i  *  p.q.i
|Divide:     RETURN p.p.i DIV p.q.i
|Modulo:     RETURN p.p.i MOD p.q.i
|And:        RETURN BoolVal((p.p.i # 0) &  (p.q.i # 0))
|Or:         RETURN BoolVal((p.p.i # 0) OR (p.q.i # 0))
|Equal:      RETURN BoolVal(p.p.i = p.q.i)
|Match:      MatchPattern(p.p, p.q); RETURN BoolVal((p.p.i = p.q.i) & ~More(p.q))  (* Whether key is entirely matched *)
|Merge:      RETURN EvaluateMerge(p)
|Over:       RETURN EvaluateOver(p)
ELSE         w.s("Evaluate passed unexpected kind "); wkind(p.kind); Fail(".")
END END Evaluate;

PROCEDURE ResetObject(p: Ptr): Int;
BEGIN
  CASE p.kind OF
  |Integer: RETURN p.i
  |Iota:    Reset(p.p);  p.i := p.p.i;  RETURN 0
  |Repeat:  Reset(p.p);  Reset(p.q);  p.i := 0;  RETURN p.p.i;
  |Over:    Reset(p.p);  RETURN EvaluateOver(p);
  ELSE      Reset(p.p);  Reset(p.q);  RETURN Evaluate(p)
  END
END ResetObject;

PROCEDURE Reset(VAR p: Ptr);
BEGIN IF p # NIL THEN
  Assert(p.kind # Nobj, "Attempt to reset Nobj.");
  IF p.kind # Stepper THEN p := NewObj(Stepper, p, 0) END;
  p.q := p.p;
  p.i := ResetObject(p.q)
END END Reset;

PROCEDURE More(p: Ptr): BOOLEAN;
BEGIN
  IF p = NIL THEN RETURN FALSE END;
  IF p.kind # Stepper THEN w.s("Expected stepper in More, got "); wkind(p.kind); w.sl(".") END;
  IF p.q.n # NIL THEN RETURN TRUE END;
  CASE p.q.kind OF
  |Integer, Match, Merge, Over: RETURN FALSE
  |Iota:    RETURN p.i < p.q.i-1
  |Repeat:  RETURN (p.q.i < p.q.q.i-1) OR More(p.q.p)
  ELSE      RETURN More(p.q.p) OR More(p.q.q)
  END;
RETURN FALSE END More;

PROCEDURE Next(p: Ptr);
BEGIN
  IF p.kind # Stepper THEN w.s("Expected stepper in Next, got "); wkind(p.kind); w.sl(".") END;
  Assert(p.q.n # NIL, "Expected non-nil p.q.n in Next");
  p.q := p.q.n;
  p.i := ResetObject(p.q)
END Next;

PROCEDURE Advance(p: Ptr);
BEGIN IF p # NIL THEN
  IF p.kind # Stepper THEN w.s("Expected stepper in Advance, got "); wkind(p.kind); w.sl(".") END;
  IF ~More(p) THEN RETURN END;
  CASE p.q.kind OF
  |Integer: Next(p)
  |Iota:    IF p.i < p.q.i-1 THEN INC(p.i) ELSE Next(p) END
  |Repeat:  IF More(p.q.p) THEN
              Advance(p.q.p); p.i := p.q.p.i
            ELSIF p.q.i < p.q.q.i-1 THEN
              Reset(p.q.p); INC(p.q.i); p.i := p.q.p.i
            ELSE
              Next(p)
            END;
  ELSE      IF More(p.q.p) OR More(p.q.q) THEN
              Advance(p.q.p);  Advance(p.q.q);  p.i := Evaluate(p.q)
            ELSE
              Next(p)
            END
  END
END END Advance;

(* ------------------------------------------------------------------------ *)

PROCEDURE ImportUTF8(s: ARRAY [1] OF CHAR): Ptr;
VAR i: Int;  first, last: Ptr;

  PROCEDURE ParseUTF8(): Int;
  VAR c, l, n: Int;
  BEGIN
    Assert(i < LEN(s), "ParseUTF8 expects at least one character remaining in input.");
    c := ORD(s[i]);  INC(i);
    IF c >= 128 THEN (* Multi-byte UTF-8 encoding *)
      n := c DIV 16 MOD 4;  (* 0,1: 1 byte follows; 2: 2 bytes; 3 3 bytes. *)
      IF n < 2 THEN c := c MOD 32; l := i+1 ELSE c := c MOD 16; l := i+n END;
      (* c is most sig bits, l is limit of following bytes. *)
      IF l > LEN(s) THEN c := 0FFFDH; i := LEN(s)  (* Malformed *)
      ELSE
        WHILE (i < l) & (ORD(s[i]) DIV 64 = 2) DO
          c := c*64 + ORD(s[i]) MOD 64;  INC(i)
        END;
        IF i # l THEN c := 0FFFDH
        ELSE
          CASE n OF
          |3:  IF (c < 10000H) OR (c > 10FFFFH) THEN c := 0FFFDH END
          |2:  IF (c < 800H) OR (c >= 0D800H) & (c <= 0DFFFH) THEN c := 0FFFDH END
          ELSE IF c < 80H THEN c := 0FFFDH END
          END
        END
      END
    END;
  RETURN c END ParseUTF8;

BEGIN i := 0;
  IF (LEN(s) = 0) OR (s[0] = 0X) THEN RETURN NIL END;
  first := NewObj(Integer, NIL, ParseUTF8());
  last := first;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO
    last.n := NewObj(Integer, NIL, ParseUTF8());
    last := last.n
  END;
RETURN first END ImportUTF8;


PROCEDURE Parse(s: ARRAY [1] OF CHAR): Ptr;
VAR
  characters, token, tree: Ptr;

  PROCEDURE IntegerToken;
  VAR acc: Int;
  BEGIN acc := characters.i - 30H;
    WHILE (characters.n   #  NIL)
        & (characters.n.i >= 30H)
        & (characters.n.i <= 39H) DO
      characters := characters.n;
      acc := acc*10 + characters.i - 30H
    END;
    token      := characters;
    token.i    := acc;
    characters := characters.n;
    token.n    := NIL;
  END IntegerToken;


  PROCEDURE ClassifyDelim(delim: Int): Int;  (* 0 - not delim, 1 - terminal delim, 2 - double delim *)
  BEGIN
    IF characters     = NIL   THEN RETURN 1 END;
    IF characters.i   # delim THEN RETURN 0 END;
    IF characters.n   = NIL   THEN RETURN 1 END;
    IF characters.n.i # delim THEN RETURN 1 END;
    RETURN 2
  END ClassifyDelim;

  PROCEDURE StringToken;
  VAR  delim, class: Int;  last: Ptr;
  BEGIN
    (* w.lc; w.sl("StringToken."); *)
    IF (characters.n = NIL) THEN
      token := characters;  token.i := -1;  characters := NIL
    ELSE
      delim := characters.i;  characters := characters.n;
      token := characters;
      class := ClassifyDelim(delim);
      IF class = 1 THEN  (* empty string *)
        token.i := -1;  characters := characters.n;  token.n := NIL
      ELSE
        WHILE class # 1 DO
          IF class = 2 THEN characters.n := characters.n.n END;
          last := characters;  characters := characters.n;
          class := ClassifyDelim(delim);
        END;
        characters := characters.n;
        (* w.sl("Set NIL!"); *)
        last.n := NIL
      END
    END;
    (* w.sl("StringToken complete."); *)
  END StringToken;

  PROCEDURE OperatorToken(leading: BOOLEAN);
  VAR  op: Int;  spaceAfter: BOOLEAN;
  BEGIN
    spaceAfter := (characters.n = NIL) OR (characters.n.i <= 20H);

    IF leading = spaceAfter THEN  (* Infix *)
      characters.kind := Infix;
      CASE characters.i OF
      |3DH:  (* = *) characters.i := Equal
      |3FH:  (* ? *) characters.i := Match
      |21H:  (* ! *) characters.i := Merge
      |2BH:  (* + *) characters.i := Add
      |2DH:  (* - *) characters.i := Subtract
      |2AH:  (* * *) characters.i := Multiply
      |2FH:  (* / *) characters.i := Divide
      |25H:  (* % *) characters.i := Modulo
      |26H:  (* & *) characters.i := And
      |7CH:  (* | *) characters.i := Or
      |72H:  (* r *) characters.i := Repeat
      ELSE w.s("Unrecognised infix operator '"); w.c(CHR(characters.i)); w.s("'."); Fail("");
      END;
    ELSIF leading THEN  (* Prefix *)
      characters.kind := Prefix;
      CASE characters.i OF
      |28H:  (* ( *) characters.i := Open
      |7EH:  (* ~ *) characters.i := Not
      |0ACH: (* ¬ *) characters.i := Not
      |69H:  (* i *) characters.i := Iota
      |2BH:  (* + *) characters.i := Identity
      |2DH:  (* - *) characters.i := Negate
      |2FH:  (* / *) characters.i := Over
      ELSE w.s("Unrecognised prefix operator '"); w.c(CHR(characters.i)); w.s("'."); Fail("");
      END;
    ELSE  (* Postfix *)
      characters.kind := Postfix;
      CASE characters.i OF
      |21H:  (* ! *) characters.i := Factorial
      |29H:  (* ) *) characters.i := Close
      ELSE w.s("Unrecognised postfix operator '"); w.c(CHR(characters.i)); w.s("'."); Fail("");
      END;
    END;
    token      := characters;
    characters := characters.n;
    token.n    := NIL
  END OperatorToken;

  PROCEDURE ParseToken(leading: BOOLEAN);
  BEGIN
    token := NIL;
    WHILE (characters # NIL) & (characters.i <= 20H) DO
      leading := TRUE;
      characters := characters.n
    END;
    IF characters # NIL THEN
      CASE characters.i OF
      |30H..39H:  IntegerToken   (* 0..9 *)
      |22H,27H:   StringToken    (* ' " *)
      ELSE        OperatorToken(leading)
      END
    END;
    leading := FALSE;
  END ParseToken;

  PROCEDURE^ ParseExpression(priority: Int): Ptr;  (* close - terminating character *)

  PROCEDURE ParseScalar(): Ptr;
  VAR scalar, postfix: Ptr;
  BEGIN
    Assert(token # NIL, "Expected token.");
    Assert((token.kind = Prefix) OR (token.kind = Integer), "Expected scalar");
    scalar := token;
    IF scalar.kind = Prefix THEN
      IF scalar.i = Open THEN
        ParseToken(TRUE);  scalar := ParseExpression(0)
      ELSE
        scalar.kind := scalar.i;  scalar.i := 0;  scalar.n := NIL;
        ParseToken(TRUE);  (* Parse in continuing prefix context *)
        scalar.p := ParseScalar()
      END
    ELSE
      ParseToken(FALSE)
    END;
    WHILE (token # NIL) & (token.kind = Postfix) & (token.i # Close) DO
      token.kind := token.i;  token.i := 0;
      token.p := scalar;  scalar := token;
      token := token.n;  scalar.n := NIL;
    END;
  RETURN scalar END ParseScalar;

  PROCEDURE Last(p: Ptr): Ptr;
  VAR last: Ptr;
  BEGIN last := p;
    WHILE last.n # NIL DO last := last.n END;
  RETURN last END Last;

  PROCEDURE ParseOperand(): Ptr;
  VAR operand, last: Ptr;
  BEGIN
    operand := ParseScalar();
    last := Last(operand);
    WHILE (token # NIL) & ((token.kind = Prefix) OR (token.kind = Integer)) DO
      last.n := ParseScalar();  last := Last(last.n)
    END;
  RETURN operand END ParseOperand;

  PROCEDURE Pri(kind: Int): Int;  (* Infix operator priority *)
  BEGIN
    CASE kind OF
    |Nobj:      RETURN 0
    |Equal:     RETURN 1
    |Match:     RETURN 1
    |Add:       RETURN 2
    |Subtract:  RETURN 2
    |Merge:     RETURN 2
    |Multiply:  RETURN 3
    |Divide:    RETURN 3
    |Modulo:    RETURN 3
    |And:       RETURN 3
    |Or:        RETURN 3
    |Repeat:    RETURN 4
    ELSE w.s("Priority passed unexpected kind "); wkind(kind); w.s("."); Fail("");
    END
  END Pri;

  PROCEDURE ParseExpression(priority: Int): Ptr;  (* close - terminating character *)
  VAR left, right, expression: Ptr;
  BEGIN
    left := ParseOperand();
    WHILE (token # NIL) & (token.kind = Infix) & (Pri(token.i) >= priority) DO
      expression      := token;
      expression.kind := expression.i;
      expression.i    := 0;
      ParseToken(TRUE);
      expression.p    := left;
      expression.q    := ParseExpression(Pri(expression.kind)+1);
      left := expression;
    END;
  RETURN left END ParseExpression;

BEGIN tree := NIL;
  (* w.sl("Parse."); *)
  characters := ImportUTF8(s);
  (* w.s("Characters imported, first character "); w.i(characters.i); w.sl("."); *)
  IF characters # NIL THEN
    ParseToken(TRUE);
    tree := ParseExpression(0)
  END;
RETURN tree END Parse;


(* ------------------------------------------------------------------------ *)

PROCEDURE Print(p: Ptr);
BEGIN
  Reset(p);  w.i(p.i);  WHILE More(p) DO Advance(p); w.i(p.i) END
END Print;

PROCEDURE^ PrintTree(p: Ptr; indent: Int);
PROCEDURE PrintPtr(label: ARRAY [1] OF CHAR; p,q: Ptr; indent: Int);
BEGIN
  IF q # NIL THEN
    w.space(indent); w.s(label);
    IF q = p THEN w.sl("self.") ELSE PrintTree(q, indent+3) END
  END
END PrintPtr;

PROCEDURE PrintTree(p: Ptr; indent: Int);
BEGIN
  Assert(indent < 100, "PrintTree expectes indent < 100.");
  wkind(p.kind); w.s(": "); w.i(p.i); w.l;
  PrintPtr("p: ", p, p.p, indent);
  PrintPtr("q: ", p, p.q, indent);
  PrintPtr("n: ", p, p.n, indent);
END PrintTree;

PROCEDURE ColCount(s: ARRAY [1] OF CHAR): Int;
VAR i, c: Int;
BEGIN i := 0;  c := 0;
  WHILE (i < LEN(s)) & (s[i] # 0X) DO
    INC(i);  INC(c);
    IF ORD(s[i-1]) DIV 64 = 3 THEN (* First byte of UTF-8 sequence *)
      WHILE (i < LEN(s)) & (ORD(s[i]) >= 128) & (ORD(s[i]) < 192) DO INC(i) END
    END;
  END;
RETURN c END ColCount;

PROCEDURE^ PriorityParse(s: ARRAY OF CHAR): Ptr;

PROCEDURE TestPriorityParse(ind: Int; s: ARRAY OF CHAR);
VAR i: Int;
BEGIN
  w.s('  "'); w.s(s); w.s('" ');
  i := ColCount(s);  WHILE i < ind DO w.c(' '); INC(i) END;
  Print(PriorityParse(s)); w.l;
END TestPriorityParse;

PROCEDURE TestParse(ind: Int; s: ARRAY OF CHAR);
VAR  i: Int;  p: Ptr;
BEGIN
  IF TRUE THEN
    w.s('  "'); w.s(s); w.s('" ');
    i := ColCount(s);  WHILE i < ind DO w.c(' '); INC(i) END;
    p := Parse(s);
    w.s('➜  ');  Print(p);  w.l;
  ELSE
    w.l; w.s('Parse "'); w.s(s); w.sl('".');
    p := Parse(s);
    w.sl("Before Reset:");  w.s("  ");  PrintTree(p, 2);
    Reset(p);
    w.sl("After Reset:");   w.s("  ");  PrintTree(p, 2);
    w.s('"'); w.s(s); w.sl('" ->');
    w.s("[0] "); w.i(p.i); w.l;
    IF More(p) THEN
      i := 1;  Advance(p);
      w.sl("After Advance:");   w.s("  ");  PrintTree(p, 2);
      w.s("[1] "); w.i(p.i); w.l;
      WHILE (i < 9) & More(p) DO
        INC(i);  Advance(p);
        w.s("["); w.i(i); w.s("] "); w.i(p.i); w.l
      END;
      IF i = 9 THEN w.sl(".. Stopped at 9 iterations.") END
    END
  END
END TestParse;

PROCEDURE TestParserTwo;
BEGIN
  w.l; w.sl("Parser two:");
  TestParse(20, "1                 ");
  TestParse(20, "+8                ");
  TestParse(20, "-1                ");
  TestParse(20, "--1               ");
  TestParse(20, "3!                ");
  TestParse(20, "-3!               ");
  TestParse(20, "1 +2              ");
  TestParse(20, "1 + 2             ");
  TestParse(20, "1+2               ");
  TestParse(20, "1+2+3             ");
  TestParse(20, "1 + 2 - (5 - 1)   ");
  TestParse(20, "1+2-(5-1)         ");
  TestParse(20, "1-2-3-4           ");
  TestParse(20, "2*3+1             ");
  TestParse(20, "1+2*3             ");
  TestParse(20, "1+2*3+4           ");
  TestParse(20, "1 1               ");
  TestParse(20, "-1 1              ");
  TestParse(20, "1 -1              ");
  TestParse(20, "1 -1 1            ");
  TestParse(20, "1 2 3 4           ");
  TestParse(20, "1 -2 3 -4 5       ");
  TestParse(20, "1 2 + 3 4         ");
  TestParse(20, "1 2 3 4 + 10      ");
  TestParse(20, "(2)               ");
  TestParse(20, "1 -(2 3)          ");
  TestParse(20, "'AB' 'CD ¬¦é€£'   ");
  TestParse(20, "-'AB'             ");
  TestParse(20, "i4                ");
  TestParse(20, "i4+1              ");
  TestParse(20, "1+2*i4            ");
  TestParse(20, "1+i4*2            ");
  TestParse(20, "1 2 3 4 r 3       ");
  TestParse(20, "i4r3              ");

  (* TestParse(20, "/+5               "); *)
  (* TestParse(20, "/+i5              "); *)
  (* TestParse(20, "/-i5              "); *)
  (* TestParse(20, "/*i5              "); *)
  (* TestParse(20, "/*(i5+1)          "); *)
  (* TestParse(20, "/+ 5 15 27        "); *)
  TestParse(20, "''                ");
  TestParse(20, "'A'               ");
  TestParse(20, "'123'             ");
  TestParse(20, '"123"             ');
  TestParse(20, '"!""#"            ');
  TestParse(20, '"¬¦é€£"           ');
  TestParse(20, "1 2 3 4 = 1 3 2 4 ");
  TestParse(20, "'abcde' = 'axcxe' ");
  TestParse(20, "1 2 3 ? 1 2 3     ");
  TestParse(20, "1 2 3 4 ? 1 9 9 4 ");
  TestParse(20, "1 2 3 4 ? 1 2     ");
  TestParse(20, "1 2 ? 1 2 3 4     ");
  TestParse(20, "i4 ? 0 1 2 3      ");
  TestParse(20, "0 1 2 3 ? i4      ");
  TestParse(20, "'abc' ! 'alpha'   ");
  TestParse(20, "'abc' ! 'beta'    ");
  TestParse(20, "'abc' ! 'abc'     ");
  TestParse(20, "t                 ");
  TestParse(20, "t ! 'a'           ");
  TestParse(20, "t ! 'alpha'       ");
  TestParse(20, "t ! 'beta'        ");
  TestParse(20, "t ! 'abc'         ");
  TestParse(20, "t ! 'abc'         ");
  TestParse(20, "t ? 'abc'         ");
  TestParse(20, "t ! 'a'           ");


END TestParserTwo;


(* ------------------------------------------------------------------------ *)

PROCEDURE PriorityParse(s: ARRAY OF CHAR): Ptr;

VAR i: Int;

  PROCEDURE ParseUTF8(): Int;
  VAR c, l, n: Int;
  BEGIN
    c := ORD(s[i]);  INC(i);
    IF (i < LEN(s)) & (c >= 128) THEN (* Multi-byte UTF-8 encoding *)
      n := c DIV 16 MOD 4;  (* 0,1: 1 byte follows; 2: 2 bytes; 3 3 bytes. *)
      IF n < 2 THEN c := c MOD 32; l := i+1 ELSE c := c MOD 16; l := i+n END;
      (* c is most sig bits, l is limit of following bytes. *)
      IF l > LEN(s) THEN c := 0FFFDH; i := LEN(s)
      ELSE
        WHILE (i < l) & (ORD(s[i]) DIV 64 = 2) DO
          c := c*64 + ORD(s[i]) MOD 64;  INC(i)
        END;
        IF i # l THEN c := 0FFFDH
        ELSE
          CASE n OF
          |3:  IF (c < 10000H) OR (c > 10FFFFH) THEN c := 0FFFDH END
          |2:  IF (c < 800H) OR (c >= 0D800H) & (c <= 0DFFFH) THEN c := 0FFFDH END
          ELSE IF c < 80H THEN c := 0FFFDH END
          END
        END
      END
    END;
  RETURN c END ParseUTF8;

  PROCEDURE ParseChar(delim: Int): Int;  (* returns 0 at end *)
  VAR c: Int;
  BEGIN
    IF i >= LEN(s) THEN RETURN 0 END;
    IF ORD(s[i]) = delim THEN
      INC(i);
      IF (i < LEN(s)) & (ORD(s[i]) = delim) THEN
        INC(i);  c := delim
      ELSE
        c := 0
      END
    ELSE
      c := ParseUTF8()
    END;
  RETURN c END ParseChar;

  PROCEDURE ParseString(delim: Int): Ptr;
  VAR  result, current: Ptr;  c: Int;
  BEGIN
    c := ParseChar(delim);
    result := NewObj(Integer, NIL, c);
    IF c # 0 THEN
      current := result;
      c := ParseChar(delim);
      WHILE c # 0 DO
        current.n := NewObj(Integer, NIL, c);
        current := current.n;
        c := ParseChar(delim);
      END
    END;
  RETURN result END ParseString;


  PROCEDURE skipSpace;
  BEGIN WHILE (i < LEN(s))  &  (s[i] > 0X)  &  (s[i] <= ' ') DO INC(i) END
  END skipSpace;

  PROCEDURE expect(c: CHAR);
  BEGIN skipSpace;
    Assert(s[i] = c, "Unexpected character in PriorityParse");
    INC(i)
  END expect;

  PROCEDURE ParseInt(VAR s: ARRAY OF CHAR; VAR i: Int): Int;
  VAR acc: Int;
  BEGIN acc := 0;
    WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
      acc := acc*10 + ORD(s[i]) - ORD('0');  INC(i)
    END;
  RETURN acc END ParseInt;

  PROCEDURE ParseIntegers(): Ptr;
  VAR result, current: Ptr;
  BEGIN
    result := NewObj(Integer, NIL, ParseInt(s, i));  skipSpace;
    IF (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') THEN
      current := result;
      WHILE (i < LEN(s)) & (s[i] >= '0') & (s[i] <= '9') DO
        current.n := NewObj(Integer, NIL, ParseInt(s, i));
        current := current.n;  skipSpace
      END
    END;
  RETURN result END ParseIntegers;


  PROCEDURE^ ParseDyadic(priority: Int): Ptr;

  PROCEDURE ParseOperation(VAR op: OpDef);
  BEGIN  skipSpace;  op := Ops[ORD(s[i])]  END ParseOperation;

  PROCEDURE ParseOperand(): Ptr;
  VAR  result, link: Ptr;  op: OpDef;  val: Int;
  BEGIN skipSpace;
    CASE s[i] OF
    |'(':      INC(i);  result := ParseDyadic(0);  skipSpace;  expect(')')
    |'/':      INC(i);  ParseOperation(op);
               Assert(op.dyadic # Nobj, "Expected dyadic operator following '/'.");
               INC(i);
               result := NewObj(Over, ParseOperand(), 0);
               result.q := NewObj(op.dyadic, NIL, 0)
    |'0'..'9': result := ParseIntegers()
    |'"':      INC(i);  result := ParseString(ORD('"'))
    |"'":      INC(i);  result := ParseString(ORD("'"))
    |'t':      INC(i);  result := Tree;
    ELSE       ParseOperation(op);  INC(i);
               IF op.prefix = Identity THEN result := ParseOperand()
               ELSE result := NewObj(op.prefix, ParseOperand(), 0) END
    END;
  RETURN result END ParseOperand;


  PROCEDURE ParseDyadic(priority: Int): Ptr;
  VAR  p: Ptr;  op: OpDef;
  BEGIN  p := ParseOperand();
    ParseOperation(op);
    WHILE op.priority >= priority DO
      INC(i);
      p   := NewObj(op.dyadic, p, 0);
      p.q :=  ParseDyadic(op.priority+1);
      ParseOperation(op)
    END;
  RETURN p END ParseDyadic;

BEGIN i := 0;
  RETURN ParseDyadic(0)
END PriorityParse;



(*--------------------------------------------------------------------------*)

PROCEDURE TestParserOne;
BEGIN
  Tree := NewObj(Integer, NIL, ORD('/'));

  w.sl("Parser one:");

  (*
  TestPriorityParse(50, "1                 ");
  TestPriorityParse(50, "1+2               ");
  TestPriorityParse(50, "1+2+3             ");
  TestPriorityParse(50, "1+2-(5-1)         ");
  TestPriorityParse(50, "1-2-3-4           ");
  TestPriorityParse(50, "2*3+1             ");
  TestPriorityParse(50, "1+2*3             ");
  TestPriorityParse(50, "1+2*3+4           ");
  TestPriorityParse(50, "1 2 3 4           ");
  TestPriorityParse(50, "1 2 + 3 4         ");
  TestPriorityParse(50, "1 2 3 4 + 10      ");
  TestPriorityParse(50, "i4                ");
  TestPriorityParse(50, "i4+1              ");
  TestPriorityParse(50, "1+2*i4            ");
  TestPriorityParse(50, "1+i4*2            ");
  TestPriorityParse(50, "1 2 3 4 r 3       ");
  TestPriorityParse(50, "i4r3              ");
  TestPriorityParse(50, "/+5               ");
  TestPriorityParse(50, "/+i5              ");
  TestPriorityParse(50, "/-i5              ");
  TestPriorityParse(50, "/*i5              ");
  TestPriorityParse(50, "/*(i5+1)          ");
  TestPriorityParse(50, "/+ 5 15 27        ");
  TestPriorityParse(50, "''                ");
  TestPriorityParse(50, "'A'               ");
  TestPriorityParse(50, "'123'             ");
  TestPriorityParse(50, '"123"             ');
  TestPriorityParse(50, '"!""#"            ');
  TestPriorityParse(50, '"¬¦é€£"           ');
  TestPriorityParse(50, "1 2 3 4 = 1 3 2 4 ");
  TestPriorityParse(50, "'abcde' = 'axcxe' ");
  TestPriorityParse(50, "1 2 3 ? 1 2 3     ");
  TestPriorityParse(50, "1 2 3 4 ? 1 9 9 4 ");
  TestPriorityParse(50, "1 2 3 4 ? 1 2     ");
  TestPriorityParse(50, "1 2 ? 1 2 3 4     ");
  TestPriorityParse(50, "i4 ? 0 1 2 3      ");
  TestPriorityParse(50, "0 1 2 3 ? i4      ");
  TestPriorityParse(50, "'abc' ! 'alpha'   ");
  TestPriorityParse(50, "'abc' ! 'beta'    ");
  TestPriorityParse(50, "'abc' ! 'abc'     ");
  TestPriorityParse(50, "t                 ");
  TestPriorityParse(50, "t ! 'a'           ");
  TestPriorityParse(50, "t ! 'alpha'       ");
  TestPriorityParse(50, "t ! 'beta'        ");
  TestPriorityParse(50, "t ! 'abc'         ");
  TestPriorityParse(50, "t ! 'abc'         ");
  TestPriorityParse(50, "t ? 'abc'         ");
  TestPriorityParse(50, "t ! 'a'           ");
  Tree := NewObj(Integer, NIL, ORD('/'));
  *)

  TestPriorityParse(50, "/&( 1                 = 1 )");
  TestPriorityParse(50, "/&( 1+2-(5-1)         = -1 )");
  TestPriorityParse(50, "/&( 1-2-3-4           = -8 )");
  TestPriorityParse(50, "/&( 2*3+1             = 7 )");
  TestPriorityParse(50, "/&( 1+2*3             = 7 )");
  TestPriorityParse(50, "/&( 1+2*3+4           = 11 )");
  TestPriorityParse(50, "/&( 1 2 3 4           = 1 2 3 4 )");
  TestPriorityParse(50, "/&( 1 2 + 3 4         = 4 6 )");
  TestPriorityParse(50, "/&( 1 2 3 4 + 10      = 11 12 13 14 )");
  TestPriorityParse(50, "/&( i4                = 0 1 2 3 )");
  TestPriorityParse(50, "/&( i4+1              = 1 2 3 4 )");
  TestPriorityParse(50, "/&( 1+2*i4            = 1 3 5 7 )");
  TestPriorityParse(50, "/&( 1+i4*2            = 1 3 5 7 )");
  TestPriorityParse(50, "/&( 1 2 3 4 r 3       = 1 2 3 4 1 2 3 4 1 2 3 4 )");
  TestPriorityParse(50, "/&( i4r3              = 0 1 2 3 0 1 2 3 0 1 2 3 )");
  TestPriorityParse(50, "/&( /+5               = 5 )");
  TestPriorityParse(50, "/&( /+i5              = 10 )");
  TestPriorityParse(50, "/&( /-i5              = -10 )");
  TestPriorityParse(50, "/&( /*i5              = 0 )");
  TestPriorityParse(50, "/&( /*(i5+1)          = 120 )");
  TestPriorityParse(50, "/&( /+ 5 15 27        = 47 )");
  TestPriorityParse(50, "/&( ''                = 0 )");
  TestPriorityParse(50, "/&( 'A'               = 65 )");
  TestPriorityParse(50, "/&( '123'             = 49 50 51 )");
  TestPriorityParse(50, '/&( "123"             = 49 50 51 )');
  TestPriorityParse(50, '/&( "!""#"            = 33 34 35 )');
  TestPriorityParse(50, '/&( "¬¦é€£"           = 172 166 233 8364 163 )');
  TestPriorityParse(50, "/&( 1 2 3 4 = 1 3 2 4 = 1 0 0 1 )");
  TestPriorityParse(50, "/&( 'abcde' = 'axcxe' = 1 0 1 0 1 )");
  TestPriorityParse(50, "/&( 1 2 3 ? 1 2 3     = 1 )");
  TestPriorityParse(50, "/&( 1 2 3 4 ? 1 9 9 4 = 0 )");
  TestPriorityParse(50, "/&( i4 ? 0 1 2 3      = 1 )");
  TestPriorityParse(50, "/&( 0 1 2 3 ? i4      = 1 )");
  TestPriorityParse(50, "/&( 'abc' ! 'alpha'   = 1 )");
  TestPriorityParse(50, "/&( 'abc' ! 'beta'    = 1 )");
  TestPriorityParse(50, "/&( 'abc' ! 'abc'     = 0 )");
  TestPriorityParse(50, "/&( t                 = 47 )");
  TestPriorityParse(50, "/&( t ! 'a'           = 1 )");
  TestPriorityParse(50, "/&( t ! 'alpha'       = 1 )");
  TestPriorityParse(50, "/&( t ! 'beta'        = 1 )");
  TestPriorityParse(50, "/&( t ! 'abc'         = 1 )");
  TestPriorityParse(50, "/&( t ! 'abc'         = 0 )");
  TestPriorityParse(50, "/&( t ? 'abc'         = 1 )");

  TestPriorityParse(50, "t ? 'al'");
  TestPriorityParse(50, "t ? 'be'");

  TestPriorityParse(50, "/&( t ? 'al'          = 112 104 97 )");
  TestPriorityParse(50, "/&( t ? 'be'          = 116 97 )");
END TestParserOne;


PROCEDURE Test*;
BEGIN
  TestParserOne;
  TestParserTwo
END Test;

(* ------------------------------------------------------------------------ *)

PROCEDURE DefOp(c: CHAR; prefix, dyadic, priority: Int);
BEGIN
  Ops[ORD(c)].prefix   := prefix;
  Ops[ORD(c)].dyadic   := dyadic;
  Ops[ORD(c)].priority := priority
END DefOp;

PROCEDURE InitOpLevel;
VAR i: Int;
BEGIN
  FOR i := 0 TO 127 DO
    Ops[i].prefix   := Nobj;
    Ops[i].dyadic   := Nobj;
    Ops[i].priority := -1
  END;

  (*         Prefix    Dyadic   Priority *)
  DefOp('~', Not,      Nobj,    -1);
  DefOp('i', Iota,     Nobj,    -1);
  DefOp('=', Nobj,     Equal,    0);
  DefOp('?', Nobj,     Match,    0);
  DefOp('!', Nobj,     Merge,    1);
  DefOp('+', Identity, Add,      1);
  DefOp('-', Negate,   Subtract, 1);
  DefOp('*', Nobj,     Multiply, 2);
  DefOp('/', Nobj,     Divide,   2);
  DefOp('%', Nobj,     Modulo,   2);
  DefOp('&', Nobj,     And,      2);
  DefOp('|', Nobj,     Or,       2);
  DefOp('r', Nobj,     Repeat,   3)
END InitOpLevel;

BEGIN  InitOpLevel;  Tree := NewObj(Integer, NIL, ORD('/'))
END Jobs.


------------------------------------------------------------------------------


PROCEDURE wtree(p: Ptr; nest: Int);
BEGIN
  IF p = NIL THEN w.sl("NIL.") END;
  wkind(p.kind); w.s(" i="); w.nb; w.i(p.i); w.l;
  IF p.p # NIL THEN
    w.lc; w.space(nest*4); w.s("p: "); wtree(p.p, nest+1)
  END;
  IF p.q # NIL THEN
    w.lc; w.space(nest*4); w.s("q: "); wtree(p.q, nest+1)
  END;
END wtree;
