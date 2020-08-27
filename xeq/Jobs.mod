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

  (* Monadic operators *)
  Negate    = 8;    (* monadic operators                   *)
  Not       = 9;
  Square    = 10;
  Identity  = 11;
  Factorial = 12;
  Sum       = 13;
  Product   = 14;

  (* Dyadic operators *)
  Add       = 15;
  Subtract  = 16;
  Multiply  = 17;
  Divide    = 18;
  Power     = 19;
  Modulo    = 20;
  And       = 21;
  Or        = 22;
  Equal     = 23;   (* returns 0s and 1s                   *)

  (* Reduction operators *)
  Match     = 24;   (* walk match tree                     *)
  Merge     = 25;   (* merge into match tree               *)

  (* Tokens *)
  Open      = 26;   (* Parse of '(' *)
  Close     = 27;   (* Parse of ')' *)

  ObjLimit  = 28;


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

VAR
  Tree:     Ptr;
  NilToken: Ptr;

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
|Stepper:   w.s("Stepper")
|Negate:    w.s("Negate")
|Not:       w.s("Not")
|Square:    w.s("Square")
|Identity:  w.s("Identity")
|Factorial: w.s("Factorial")
|Sum:       w.s("Sum")
|Product:   w.s("Product")
|Add:       w.s("Add")
|Subtract:  w.s("Subtract")
|Multiply:  w.s("Multiply")
|Divide:    w.s("Divide")
|Modulo:    w.s("Modulo")
|And:       w.s("And")
|Or:        w.s("Or")
|Equal:     w.s("Equal")
|Match:     w.s("Match")
|Merge:     w.s("Merge")
|Open:      w.s("Open")
|Close:     w.s("Close")
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
ELSE         w.s("Evaluate passed unexpected kind "); wkind(p.kind); Fail(".")
END END Evaluate;

PROCEDURE ResetObject(p: Ptr): Int;
VAR i: Int;
BEGIN
  CASE p.kind OF
  |Integer: RETURN p.i
  |Iota:    Reset(p.p);  p.i := p.p.i;  RETURN 0
  |Repeat:  Reset(p.p);  Reset(p.q);  p.i := 0;  RETURN p.q.i;
  |Product: Reset(p.p);  i := p.p.i;  WHILE (i # 0) & More(p.p) DO Advance(p.p); i := i * p.p.i END; RETURN i
  |Sum:     Reset(p.p);  i := p.p.i;  WHILE More(p.p) DO Advance(p.p); INC(i, p.p.i) END; RETURN i
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
  |Integer, Match, Merge, Product, Sum: RETURN FALSE
  |Iota:    RETURN p.i < p.q.i-1
  |Repeat:  RETURN (p.q.i < p.q.p.i-1) OR More(p.q.q)
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
  |Repeat:  IF More(p.q.q) THEN
              Advance(p.q.q); p.i := p.q.q.i
            ELSIF p.q.i < p.q.p.i-1 THEN
              Reset(p.q.q); INC(p.q.i); p.i := p.q.q.i
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
  VAR spaceAfter: BOOLEAN;
  BEGIN
    spaceAfter := (characters.n = NIL) OR (characters.n.i <= 20H);
    CASE characters.i OF
    |28H:  (* ( *) characters.kind := Open;     characters.i := 0
    |29H:  (* ) *) characters.kind := Close;    characters.i := 0

    |7EH:  (* ~ *) characters.kind := Prefix;   characters.i := Not
    |0ACH: (* ¬ *) characters.kind := Prefix;   characters.i := Not
    |69H:  (* i *) characters.kind := Prefix;   characters.i := Iota

    |2BH:  (* + *) IF leading & ~spaceAfter THEN
                     characters.kind := Prefix;   characters.i := Identity
                   ELSE
                     characters.kind := Infix;    characters.i := Add
                   END
    |2DH:  (* - *) IF leading & ~spaceAfter THEN
                     characters.kind := Prefix;   characters.i := Negate
                   ELSE
                     characters.kind := Infix;    characters.i := Subtract
                   END
    |3DH:  (* = *) characters.kind := Infix;    characters.i := Equal
    |3FH:  (* ? *) characters.kind := Infix;    characters.i := Match
    |2AH:  (* * *) characters.kind := Infix;    characters.i := Multiply
    |2FH:  (* / *) characters.kind := Infix;    characters.i := Divide
    |25H:  (* % *) characters.kind := Infix;    characters.i := Modulo
    |26H:  (* & *) characters.kind := Infix;    characters.i := And
    |7CH:  (* | *) characters.kind := Infix;    characters.i := Or
    |72H:  (* r *) characters.kind := Infix;    characters.i := Repeat
    |2CH:  (* , *) characters.kind := Infix;    characters.i := Merge

    |21H:  (* ! *) characters.kind := Postfix;  characters.i := Factorial

    ELSE
      IF    characters.i = 220FH (* ∏ *) THEN characters.kind := Prefix;  characters.i := Product
      ELSIF characters.i = 2211H (* ∑ *) THEN characters.kind := Prefix;  characters.i := Sum
      ELSIF characters.i = 2373H (* ⍳ *) THEN characters.kind := Prefix;  characters.i := Iota
      ELSIF characters.i = 2374H (* ⍴ *) THEN characters.kind := Infix;  characters.i := Repeat
      ELSE w.s("Unrecognised operator '"); w.u(characters.i); w.s("'."); Fail("")
      END
    END;
    token      := characters;
    characters := characters.n;
    token.n    := NIL;
  END OperatorToken;

  PROCEDURE ParseToken(leading: BOOLEAN);
  BEGIN
    token := NIL;
    WHILE (characters # NIL) & (characters.i <= 20H) DO
      leading := TRUE;
      characters := characters.n
    END;
    IF characters = NIL THEN token := NilToken
    ELSE
      CASE characters.i OF
      |30H..39H:  IntegerToken   (* 0..9 *)
      |22H,27H:   StringToken    (* ' " *)
      ELSE        OperatorToken(leading)
      END
    END;
    leading := FALSE;
  END ParseToken;

  PROCEDURE Last(p: Ptr): Ptr;
  VAR last: Ptr;
  BEGIN last := p;
    WHILE last.n # NIL DO last := last.n END;
  RETURN last END Last;

  PROCEDURE OperatorPriority(operator: Int): Int;
  BEGIN
    CASE operator OF
    |Power, Square:         RETURN 3;
    |Multiply, Divide, And: RETURN 2;
    |Add, Subtract, Or:     RETURN 1;
    ELSE                    RETURN 0
    END
  END OperatorPriority;

  PROCEDURE^ ParseInfixExpression(level: Int): Ptr;

  PROCEDURE ParseOneOperand(): Ptr;  (* Parses right arg of Infix op, or whole expresion *)
  VAR operand: Ptr;
  BEGIN
    IF token.kind = Prefix THEN
      (* Recursively parse through operand and postfix operations *)
      operand := token;  ParseToken(TRUE);
      operand.kind := operand.i;
      operand.p := ParseOneOperand()
    ELSE
      IF token.kind = Open THEN
        ParseToken(TRUE);
        operand := ParseInfixExpression(0);
        Assert((token.kind = Close), "Expected closing parenthesis.");
        ParseToken(FALSE)
      ELSE
        (* Expect literal or named reference *)
        CASE token.kind OF
        |Integer: operand := token;  ParseToken(FALSE);
        ELSE      Fail("Expected operand.")
        END
      END;

      (* Apply postfix operations *)
      WHILE token.kind = Postfix DO
        token.kind := token.i;  token.i := 0;
        token.p := operand;
        operand := token;
        ParseToken(FALSE)
      END
    END;
    RETURN operand
  END ParseOneOperand;

  PROCEDURE ParseOperandList(): Ptr;
  VAR operand, last: Ptr;
  BEGIN
    operand := ParseOneOperand();  last := Last(operand);
    WHILE (token.kind = Prefix)
    OR    (token.kind = Open)
    OR    (token.kind = Integer) DO
      last.n := ParseOneOperand();  last := Last(last.n)
    END;
  RETURN operand END ParseOperandList;

  PROCEDURE ParseInfixExpression(level: Int): Ptr;
  VAR expression, operator: Ptr;
  BEGIN
    expression := ParseOperandList();
    WHILE (token.kind = Infix) & (OperatorPriority(token.i) >= level) DO
      operator := token;  ParseToken(FALSE);
      operator.kind := operator.i;  operator.i := 0;
      operator.p := expression;
      operator.q := ParseInfixExpression(OperatorPriority(operator.kind)+1);
      expression := operator
    END;
  RETURN expression END ParseInfixExpression;


BEGIN tree := NIL;
  (* w.sl("Parse."); *)
  characters := ImportUTF8(s);
  (* w.s("Characters imported, first character "); w.i(characters.i); w.sl("."); *)
  IF characters # NIL THEN
    ParseToken(TRUE);
    tree := ParseInfixExpression(0)
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
  Assert(indent < 100, "PrintTree expects indent < 100.");
  wkind(p.kind); w.s(": "); w.i(p.i); w.l;
  PrintPtr("p: ", p, p.p, indent);
  PrintPtr("q: ", p, p.q, indent);
  PrintPtr("n: ", p, p.n, indent);
END PrintTree;

PROCEDURE wexpr(e: Ptr);
  PROCEDURE winfix  (op: ARRAY OF CHAR); BEGIN wexpr(e.p); w.s(op); wexpr(e.q) END winfix;
  PROCEDURE wprefix (op: ARRAY OF CHAR); BEGIN w.s(op); wexpr(e.p)             END wprefix;
  PROCEDURE wpostfix(op: ARRAY OF CHAR); BEGIN wexpr(e.p); w.c("!")            END wpostfix;
BEGIN
  IF (e.kind = Integer) & (e.n = NIL) THEN
    w.i(e.i)
  ELSE
    w.c("(");
    WHILE e # NIL DO
      CASE e.kind OF
      |Integer:    w.i(e.i)
      |Add:        winfix("+")
      |Subtract:   winfix("-")
      |Multiply:   winfix("×")
      |Divide:     winfix("÷")
      |Repeat:     winfix("⍴")
      |Equal:      winfix("=")
      |Match:      winfix("?")
      |Merge:      winfix(",")
      |Iota:       wprefix("⍳")
      |Sum:        wprefix("∑")
      |Product:    wprefix("∏")
      |Negate:     wprefix("-")
      |Identity:   wprefix("+")
      |Factorial:  wpostfix("!")
      ELSE         w.c("?")
      END;
      e := e.n;
      IF e # NIL THEN w.c(" ") END
    END;
    w.c(")")
  END
END wexpr;

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

PROCEDURE TestParse(ind: Int; s: ARRAY OF CHAR);
VAR  i: Int;  p: Ptr;
BEGIN
  IF TRUE THEN
    w.s('  "'); w.s(s); w.s('" ');
    i := ColCount(s);  WHILE i < ind DO w.c(' '); INC(i) END;
    w.s('➜  ');  w.fl;
    p := Parse(s);
    w.s("  "); wexpr(p); w.s("  = ");
    Print(p);  w.l;
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

(* ------------------------------------------------------------------------ *)

PROCEDURE Test*;
BEGIN
  TestParse(20, "1                 ");
  TestParse(20, "+8                ");
  TestParse(20, "1+2               ");
  TestParse(20, "1+2+3             ");
  TestParse(20, "2*3+1             ");
  TestParse(20, "1+2*3             ");
  TestParse(20, "1+2*3+4           ");
  TestParse(20, "0+1-2-3-4         ");
  TestParse(20, "1-2-3-4           ");
  TestParse(20, "1+2-(5-1)         ");
  TestParse(20, "1 1               ");
  TestParse(20, "(1) (1)           ");
  TestParse(20, "-1 1              ");
  TestParse(20, "1 -1              ");
  TestParse(20, "1 -1 1            ");
  TestParse(20, "1 2 3 4           ");
  TestParse(20, "1 -2 3 -4 5       ");
  TestParse(20, "1 +2              ");
  TestParse(20, "1 2 + 3 4         ");
  TestParse(20, "1 2 3 4 + 10      ");
  TestParse(20, "1 + 2             ");
  TestParse(20, "1 + 2 - (5 - 1)   ");

  TestParse(20, "1 + 2 3 + 4 5 + 6 ");
  TestParse(20, "1+2 3+4 5+6       ");
  TestParse(20, "(1+2) (3+4) (5+6) ");

  TestParse(20, "(2)               ");
  TestParse(20, "1 -(2 3)          ");
  TestParse(20, "'AB' 'CD ¬¦é€£'   ");
  TestParse(20, "-'AB'             ");

  TestParse(20, "i4                ");
  TestParse(20, "i4+1              ");
  TestParse(20, "1+2*i4            ");
  TestParse(20, "1+i4*2            ");

  TestParse(20, "3 r 1 2 3 4       ");
  TestParse(20, "3ri4              ");

  TestParse(20, "∑5                ");
  TestParse(20, "∑5 1              ");
  TestParse(20, "∑i5               ");
  TestParse(20, "∑(5 15 27)        ");
  TestParse(20, "∏i5               ");
  TestParse(20, "∏(i5+1)           ");

  TestParse(20, "''                ");
  TestParse(20, "'A'               ");
  TestParse(20, "'123'             ");
  TestParse(20, '"123"             ');
  TestParse(20, '"!""#"            ');
  TestParse(20, '"¬¦é€£"           ');
  TestParse(20, "'a'1'b'           ");

  TestParse(20, "1 2 3 4 = 1 3 2 4 ");
  TestParse(20, "'abcde' = 'axcxe' ");
  TestParse(20, "1 2 3 ? 1 2 3     ");
  TestParse(20, "1 2 3 4 ? 1 9 9 4 ");
  TestParse(20, "1 2 3 4 ? 1 2     ");
  TestParse(20, "1 2 ? 1 2 3 4     ");
  TestParse(20, "i4 ? 0 1 2 3      ");
  TestParse(20, "0 1 2 3 ? i4      ");
  TestParse(20, "'abc' , 'alpha'   ");
  TestParse(20, "'abc' , 'beta'    ");
  TestParse(20, "'abc' , 'abc'     ");

  (*
  TestParse(20, "t                 ");
  TestParse(20, "t , 'a'           ");
  TestParse(20, "t , 'alpha'       ");
  TestParse(20, "t , 'beta'        ");
  TestParse(20, "t , 'abc'         ");
  TestParse(20, "t , 'abc'         ");
  TestParse(20, "t ? 'abc'         ");
  TestParse(20, "t , 'a'           ");
  TestParse(20, "t ? 'al'");
  TestParse(20, "t ? 'be'");
  *)
  END Test;


(* ------------------------------------------------------------------------ *)

BEGIN
  Tree := NewObj(Integer, NIL, ORD('/'));
  NEW(NilToken);  NilToken.kind := Nobj;  NilToken.i := 0;
END Jobs.


------------------------------------------------------------------------------

