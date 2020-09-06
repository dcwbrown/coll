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
  None      = 0;

  (* Scalar/linked list types *)
  Integer   = 1;    (* a singleton integer value           *)

  (* Parse operator types *)
  Prefix    = 2;
  Infix     = 3;
  Postfix   = 4;

  Iota      = 5;    (* a vector of 0 up to a limit         *)
  Repeat    = 6;    (* repeats a source multiple times     *)

  List      = 7;

  (* Monadic operators *)
  Negate    = 8;    (* monadic operators                   *)
  Not       = 9;
  Square    = 10;
  Identity  = 11;
  Factorial = 12;
  Sum       = 13;
  Product   = 14;
  Dump      = 15;

  (* Dyadic operators *)
  Add       = 16;
  Subtract  = 17;
  Multiply  = 18;
  Divide    = 19;
  Power     = 20;
  Modulo    = 21;
  And       = 22;
  Or        = 23;
  Equal     = 24;   (* returns 0s and 1s                   *)

  (* Reduction operators *)
  Match     = 25;   (* walk match tree                     *)
  Merge     = 26;   (* merge into match tree               *)

  (* Tokens *)
  Open      = 27;   (* Parse of '(' *)
  Close     = 28;   (* Parse of ')' *)

  ObjLimit  = 29;


  (*  ================== object ==================
      Kind       p       q       i         j
      --------   -----   -----   -------   ------
      Integer    /       alt     value     /
      Iota       parm    /       current   max
      Repeat     parm1   parm2   current   iterno
      Negate     parm    /       current   /
      Not        parm    /       current   /
      Square     parm    /       current   /
      Add        parm1   parm2   current   /
      Subtract   parm1   parm2   current   /
      Multiply   parm1   parm2   current   /
      Divide     parm1   parm2   current   /
      List       first   current current   /
  *)

  (*  Reset   - reloads p.i with first value
      More    - returns whether there are more values available
      Advance - steps p.i to the next  value
  *)

TYPE
  Int   = SYSTEM.INT64;
  Ptr   = POINTER TO Obj;
  Obj   = RECORD  kind, i, j: Int;  n, o, p, q: Ptr  END;

VAR
  Nothing:    Ptr;
  PrefixTree: Ptr;

(* ------------------------------------------------------------------------ *)

PROCEDURE Fail(s: ARRAY OF CHAR);                   BEGIN w.Fail(s)      END Fail;
PROCEDURE Assert(t: BOOLEAN; s: ARRAY [1] OF CHAR); BEGIN w.Assert(t, s) END Assert;

(* ------------------------------------------------------------------------ *)

PROCEDURE wkind(k: Int);
BEGIN CASE k OF
|None:      w.s("None")
|Integer:   w.s("Integer")
|Prefix:    w.s("Prefix")
|Infix:     w.s("Infix")
|Postfix:   w.s("Postfix")
|Iota:      w.s("Iota")
|Repeat:    w.s("Repeat")
|List:      w.s("List")
|Negate:    w.s("Negate")
|Not:       w.s("Not")
|Square:    w.s("Square")
|Identity:  w.s("Identity")
|Factorial: w.s("Factorial")
|Sum:       w.s("Sum")
|Product:   w.s("Product")
|Dump:      w.s("Dump")
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
BEGIN Assert(kind # None, "NewObj passed object kind None.");
  NEW(obj); obj.kind := kind;
  obj.p := p;  obj.q := NIL;
  obj.i := i;  obj.j := 0;
RETURN obj END NewObj;

PROCEDURE BoolVal(b: BOOLEAN): Int;
BEGIN IF b THEN RETURN 1 ELSE RETURN 0 END END BoolVal;

PROCEDURE^ Reset(VAR p: Ptr);
PROCEDURE^ More(p: Ptr): BOOLEAN;
PROCEDURE^ Advance(p: Ptr);
PROCEDURE^ Alt(p: Ptr): BOOLEAN;
PROCEDURE^ Branch(p: Ptr);

PROCEDURE^ EvaluateMatch(p: Ptr);
PROCEDURE^ EvaluateMerge(r: Ptr);
PROCEDURE^ EvaluateDump(p: Ptr);

PROCEDURE Evaluate(p: Ptr);
BEGIN CASE p.kind OF
|List:       Fail("Evaluate passed List.");
|Negate:     p.i := -p.p.i
|Identity:   p.i := p.p.i
|Factorial:  p.i := EvaluateFactorial(p.p.i)
|Not:        p.i := BoolVal(p.p.i = 0)
|Square:     p.i := p.p.i  *  p.p.i
|Add:        p.i := p.p.i  +  p.q.i
|Subtract:   p.i := p.p.i  -  p.q.i
|Multiply:   p.i := p.p.i  *  p.q.i
|Divide:     p.i := p.p.i DIV p.q.i
|Modulo:     p.i := p.p.i MOD p.q.i
|And:        p.i := BoolVal((p.p.i # 0) &  (p.q.i # 0))
|Or:         p.i := BoolVal((p.p.i # 0) OR (p.q.i # 0))
|Equal:      p.i := BoolVal(p.p.i = p.q.i)
ELSE         w.s("Evaluate passed unexpected kind "); wkind(p.kind); Fail(".")
END END Evaluate;

PROCEDURE^ Reset(VAR p: Ptr);

PROCEDURE ResetSingle(p: Ptr);
VAR i: Int;
BEGIN IF p # NIL THEN
  CASE p.kind OF
  |None:    Fail("Attempt to reset None.")
  |Integer:
  |List:    p.q := p.p;  Reset(p.q);  p.i := p.q.i
  |Iota:    Reset(p.p);  p.i := 0;  p.j := p.p.i
  |Repeat:  Reset(p.p);  Reset(p.q);  p.i := p.q.i;  p.j := 0
  |Product: Reset(p.p);  i := p.p.i;
            WHILE (i # 0) & More(p.p) DO Advance(p.p); i := i * p.p.i END;
            p.i := i
  |Sum:     Reset(p.p);  i := p.p.i;
            WHILE More(p.p) DO Advance(p.p); INC(i, p.p.i) END;
            p.i := i
  |Match:   EvaluateMatch(p)
  |Merge:   EvaluateMerge(p)
  |Dump:    EvaluateDump(p.p);
  ELSE      Reset(p.p);  Reset(p.q);  Evaluate(p)
  END
END END ResetSingle;

PROCEDURE ForceList(VAR p: Ptr);
BEGIN IF p # NIL THEN p := NewObj(List, p, p.i);  p.q := p.p END END ForceList;

PROCEDURE Reset(VAR p: Ptr);
BEGIN IF p # NIL THEN
  ResetSingle(p);
  IF (p.n # NIL) OR (p.o # NIL) THEN ForceList(p) END
END END Reset;

PROCEDURE More(p: Ptr): BOOLEAN;
VAR result: BOOLEAN;
BEGIN result := FALSE;
  IF p # NIL THEN
    CASE p.kind OF
    |Integer, Match, Merge, Product, Sum:
    |List:    result := (p.q.n # NIL) OR More(p.q)
    |Iota:    result := p.i < p.j-1
    |Repeat:  result := (p.j < p.p.i-1) OR More(p.q)
    ELSE      result := More(p.p) OR More(p.q)
    END
  END;
RETURN result END More;

PROCEDURE Advance(p: Ptr);
BEGIN IF p # NIL THEN
  CASE p.kind OF
  |Integer:
  |List:    IF    More(p.q)   THEN  Advance(p.q)
            ELSIF p.q.n # NIL THEN  p.q := p.q.n;  ResetSingle(p.q)
            END;
            p.i := p.q.i
  |Iota:    IF p.i < p.j-1 THEN INC(p.i) END
  |Repeat:  IF More(p.q)         THEN  Advance(p.q); p.i := p.q.i
            ELSIF p.j < p.p.i-1  THEN  Reset(p.q); INC(p.j); p.i := p.q.i
            END
  ELSE      IF More(p.p) OR More(p.q) THEN
              Advance(p.p);  Advance(p.q);  Evaluate(p)
            END
  END
END END Advance;

PROCEDURE Alt(p: Ptr): BOOLEAN;
BEGIN RETURN (p # NIL) & (p.kind = List) & (p.q.o # NIL) END Alt;

PROCEDURE Branch(p: Ptr);
BEGIN
  IF (p # NIL) & (p.kind = List) & (p.q.o # NIL) THEN
    p.q := p.q.o;  p.i := p.q.i
  END
END Branch;


PROCEDURE MatchPattern(VAR p, k: Ptr);
(* Assumes pattern (p) and key (k) both already reset. *)
BEGIN
  LOOP
    WHILE (k.i # p.i) & Alt(p) DO Branch(p) END;
    IF (k.i = p.i) & More(k) & More(p) THEN
      Advance(k); Advance(p)
    ELSE
      EXIT
    END
  END
END MatchPattern;

PROCEDURE EvaluateMatch(p: Ptr);
BEGIN
  Reset(p.p);  Reset(p.q);  MatchPattern(p.p, p.q);
  p.i := BoolVal((p.p.i = p.q.i) & ~More(p.q))  (* Whether key is entirely matched *)
END EvaluateMatch;

PROCEDURE T(s: ARRAY OF CHAR);
BEGIN w.s(s); w.nb; w.fl END T;

PROCEDURE EvaluateMerge(r: Ptr);
(* TODO - handle merge into middle of iota or repeat *)
VAR p, k: Ptr;  (* Pattern and Key *)
BEGIN
  Reset(r.p);  IF r.p.kind # List THEN ForceList(r.p) END;  p := r.p;
  Reset(r.q);  IF r.q.kind # List THEN ForceList(r.q) END;  k := r.q;
  T("M");

  w.lc; w.s("Merge. p.kind "); wkind(p.kind); w.s(", p.i "); w.i(p.i);
  w.s(", k.kind "); wkind(k.kind); w.s(", k.i "); w.i(k.i); w.l;

  Assert(p.kind = List, "Expected pattern to be List at merge entry.");
  Assert(p.q # NIL, "Expected pattern to have existing current object at merge entry.");
  LOOP
    WHILE (k.i # p.i) & Alt(p) DO w.c("B"); Branch(p) END;
    IF (k.i = p.i) & More(k) & More(p) THEN
      Advance(k); Advance(p)
    ELSE
      EXIT
    END
  END;
  IF p.i = k.i THEN  (* At least partial match *)
    T("=");
    IF More(k) THEN
      Assert(p.q.n = NIL, "Expected pattern to be complete.");
      p.q.n := k.q.n;
      r.i := 1  (* Success *)
    ELSE
      (* IF ~More(p) THEN w.sl("EvaluateMerge warning: Pattern incomplete at end of key.") END; *)
      r.i := 0  (* No action taken *)
    END
  ELSE  (* Found first mismatch *)
    T("#");

    w.lc; w.s(".. insert at mismatch. p.kind "); wkind(p.kind); w.s(", p.i "); w.i(p.i);
    w.s(", k.kind "); wkind(k.kind); w.s(", k.i "); w.i(k.i); w.l;

    (* Insert current pos in key as alternate in current pos of pattern *)
    Assert(p.q # NIL, "Expected pattern to be positioned at non-match.");
    Assert(p.q.o = NIL, "Expected pattern to be position at last (or only) alternative.");
    IF k.kind = List THEN
      p.q.o := k.q
    ELSE
      p.q.o := k
    END;
    Assert(p.q.o # NIL, "Expected alternative to be non-NIL after merge.");
    r.i := 1
  END
  ;T("m")
END EvaluateMerge;

PROCEDURE DumpInner(s: ARRAY OF CHAR; o: Int; p: Ptr);
VAR q: Ptr;
BEGIN
  Assert(p.kind = List, "DumpInner expected list.");
  q := p.q.o;
  IF (p.i >= 32) & (p.i < 127) THEN s[o] := CHR(p.i) ELSE s[o] := '.' END;
  IF More(p) THEN
    Advance(p); DumpInner(s, o+1, p)
  ELSE
    s[o+1] := 0X; w.s(s); w.l
  END;
  IF q # NIL THEN
    s[o] := 0X;
    p.q := q;  p.i := q.i;  DumpInner(s, o, p)
  END
END DumpInner;

PROCEDURE EvaluateDump(p: Ptr);
VAR s: ARRAY 200 OF CHAR;
BEGIN
  s := "    ";
  Reset(p);  IF p.kind # List THEN ForceList(p) END;
  w.lc;  DumpInner(s, 4, p);
  p.i := 0;
END EvaluateDump;


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
    |2EH:  (* . *) characters.kind := Postfix;  characters.i := Dump

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

  PROCEDURE TheTreeToken;
  BEGIN  characters := characters.n;  token := PrefixTree;  END TheTreeToken;

  PROCEDURE ParseToken(leading: BOOLEAN);
  BEGIN
    token := NIL;
    WHILE (characters # NIL) & (characters.i <= 20H) DO
      leading := TRUE;
      characters := characters.n
    END;
    IF characters = NIL THEN token := Nothing
    ELSE
      CASE characters.i OF
      |30H..39H:  IntegerToken   (* 0..9 *)
      |22H,27H:   StringToken    (* ' "  *)
      |74H:       TheTreeToken   (* t    *)
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
  (* w.c("P"); w.fl; *)
  characters := ImportUTF8(s);
  (* w.s("Characters imported, first character "); w.i(characters.i); w.sl("."); *)
  IF characters # NIL THEN
    ParseToken(TRUE);
    tree := ParseInfixExpression(0)
  END;
  (* w.c("p"); w.fl; *)
RETURN tree END Parse;


(* ------------------------------------------------------------------------ *)

PROCEDURE Print(p: Ptr);
BEGIN
  Reset(p); w.i(p.i);  WHILE More(p) DO Advance(p); w.i(p.i) END
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
  PROCEDURE wpostfix(op: ARRAY OF CHAR); BEGIN wexpr(e.p); w.s(op)             END wpostfix;
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
      |Dump:       wpostfix(".")
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
  TestParse(20, "1 2               ");
  TestParse(20, "(1) (2)           ");
  TestParse(20, "-1 1              ");
  TestParse(20, "1 -1              ");
  TestParse(20, "1 -1 2            ");
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

  TestParse(20, "'abc'.            ");

  TestParse(20, "t                 ");
  TestParse(20, "t , 'a'           ");
  TestParse(20, "t.                ");
  TestParse(20, "t , 'A'           ");
  TestParse(20, "t.                ");
  TestParse(20, "t , 'alpha'       ");
  TestParse(20, "t.                ");
  TestParse(20, "t , 'beta'        ");
  TestParse(20, "t.                ");
  TestParse(20, "t , 'abc'         ");
  TestParse(20, "t.                ");
  TestParse(20, "t , 'abc'         ");
  TestParse(20, "t.                ");
  TestParse(20, "t ? 'abc'         ");
  TestParse(20, "t , 'a'           ");
  TestParse(20, "t.                ");
  TestParse(20, "t ? 'al'          ");
  TestParse(20, "t ? 'xy'          ");
  TestParse(20, "t ? 'be'          ");
END Test;


(* ------------------------------------------------------------------------ *)

BEGIN
  (* 'Nothing' is the one and only object of kind 'None' *)
  NEW(Nothing);  Nothing.kind := None;  Nothing.i := 0;  Nothing.j := 0;
  PrefixTree := (* Nothing *) NewObj(Integer, NIL, ORD('/'));
END Jobs.


------------------------------------------------------------------------------

