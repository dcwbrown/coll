MODULE prefix;

IMPORT w, a;

TYPE

  Ref = RECORD link, data, next: a.Cell END;


PROCEDURE MakeRef(link: a.Cell; VAR ref: Ref);
BEGIN
  ref.link := link;
  a.FetchAtom(link, ref.data, ref.next)
END MakeRef;

PROCEDURE RefKind(ref: Ref): INTEGER;
BEGIN RETURN SHORT(ref.next) MOD 4 END RefKind;

PROCEDURE MatchingInts(r1, r2: Ref): BOOLEAN;
BEGIN
  RETURN (RefKind(r1) = a.Int) & (RefKind(r2) = a.Int) & (r1.data = r2.data)
END MatchingInts;

PROCEDURE MatchingValues(r1, r2: Ref): BOOLEAN;
BEGIN
  RETURN (RefKind(r1) = RefKind(r2)) & (r1.data = r2.data)
END MatchingValues;

PROCEDURE AdvanceMatch(VAR i, p: Ref): BOOLEAN;
(*  entry  i,p are links to matching integers
    exit   TRUE & i,p are links to the next matching integers
    or     FALSE
           & i links to the last matching integer
           & p links to the atom after which to insert inext *)
VAR
  success: BOOLEAN;
  inext, pnext, linked: Ref;
BEGIN success := FALSE;
  w.Assert(MatchingInts(i, p), "AdvanceMatch called with non-matching ints");
  MakeRef(i.next, inext);  MakeRef(p.next, pnext);
  w.Assert(RefKind(inext) = a.Int, "Advance match inly supports ints in input string");

  WHILE ~success  &  (RefKind(pnext) = a.Link) DO
    MakeRef(pnext.data, linked);
    IF MatchingValues(inext, linked) THEN
      i := inext;  p := linked;  success := TRUE
    ELSE
      MakeRef(pnext.next, pnext)
    END
  END;

  IF ~success THEN
    IF MatchingInts(inext, pnext) THEN
      i := inext;  p := pnext;  success := TRUE
    END
  END;
RETURN success END AdvanceMatch;


(*
PROCEDURE MatchRun(VAR i, p: a.Cell);
VAR iref, pref: Ref;
BEGIN
  MakeRef(i, iref);  MakeRef(p, pref);

  WHILE (inext MOD 4 = a.Int) & (pnext MOD 4 = a.Int) & (idata = pdata) DO
    i := inext;  p := pnext;
    a.FetchAtom(i, idata, inext);
    a.FetchAtom(p, pdata, pnext);
  END
END MatchRun;
*)

END prefix.