MODULE Prefix;  IMPORT w, SYSTEM;


TYPE
  i32 = SYSTEM.INT32;  i64 = SYSTEM.INT64;

  aNode = POINTER TO Node;
  Node = RECORD END;

  aMatchNode = POINTER TO MatchNode;
  MatchNode = RECORD (Node);
    next: aNode;        (* Where to look on match *)
    alt:  aMatchNode;   (* Where to look on mismatch *)
  END;

  aCharNode = POINTER TO CharNode;
  CharNode = RECORD (MatchNode)        (* Matches and consumes specific letter *)
    ch: i32;    (* Unicode codepoint *)
  END;

  aNonLetter = POINTER TO NonLetter;
  NonLetter = RECORD (MatchNode) END;  (* Matches any non-letter *)

  ScanState = RECORD
    cur: aNode;
  END;


PROCEDURE (VAR n: MatchNode) Match(ch: i32): BOOLEAN;
BEGIN w.Fail("Abstract MatchNode.Match() called.") END Match;

PROCEDURE (VAR n: CharNode) Match(ch: i32): BOOLEAN;
BEGIN RETURN ch = n.ch END Match;

PROCEDURE (VAR n: NonLetter) Match(ch: i32): BOOLEAN;
BEGIN RETURN  (ch < ORD('A'))
          OR  (ch > ORD('z'))
          OR ((ch > ORD('Z')) & (ch < ORD('a'))) END Match;


PROCEDURE Advance(ch: i32; VAR n: aNode): BOOLEAN;
VAR  cur: aMatchNode;  match: BOOLEAN;
BEGIN match := FALSE;
  IF n IS aMatchNode THEN
    IF n(aMatchNode).Match(ch) THEN
      w.sl("  match");
      n := n(aMatchNode).next;  match := TRUE
    ELSE
      cur := n(aMatchNode).alt;
      WHILE (cur # NIL) & (~cur.Match(ch)) DO cur := cur.alt END;
      match := cur # NIL;
      IF match THEN n := cur END
    END
  END;
RETURN match END Advance;


PROCEDURE Lookup(s: ARRAY [1] OF CHAR; beg, end: i32; n: aNode);
VAR i: i32;
BEGIN
  i := beg;
  WHILE (i < end) & (n # NIL) & Advance(ORD(s[i]), n) DO INC(i) END;
END Lookup;

PROCEDURE Test;
VAR r, n: aMatchNode;  cn: aCharNode;  nl: aNonLetter;
BEGIN
  NEW(cn); cn.ch := ORD('M');  r := cn;       n := cn;
  NEW(cn); cn.ch := ORD('O');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('D');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('U');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('L');  n.next := cn;  n := cn;
  NEW(cn); cn.ch := ORD('E');  n.next := cn;  n := cn;
  NEW(nl);                     n.next := nl;  n := nl;

  Lookup("MODULE fred;", 0, 12, r);


END Test;


BEGIN Test
END Prefix.