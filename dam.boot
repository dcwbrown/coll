L
[Bootstrapping ...]WL
[-----------------]WL

[Assert: expression [message]a.!]#
[%~ [WL]? #]a:

[Some assertions:]WL

0[Expected non-zero]a.!
35=[3 not equal to 5]a.!

[Counted loop test]#
[5[[Iteration ]W "`0+W L 1- "0=~ `@? ]!#]!

[Following counted loop test, ]WS

[
  [Input echo loop test. Type a line of text: ]W
  [R"W A=~ `@?]!
]!


[Variables:
  i - input
  p - pattern
  s - sequence / alternatives
  a - Assert

  m - MatchStep
  b - BackTrack
  o - OpenMatchList
  e - Equal (temp)
]#

[OpenMatchList (pattern --)]#
[ " .`'=s: ,p:
            [ [OpenMatchList complete. s=]W s.`0+W [, Pattern=]W p.W [.]WL ]#
] o:

[MatchStep ( -- )
  Recursively matches patterns of sequences or alternatives.
  Each nest pushes the previos status onto the stack as follows:
    [2] Pattern position of link to nested pattern
    [1] Input position at start of nested pattern
    [0] Sequence state of enclosing pattern
  The outer call to MatchStep is entered with a link to NIL
    on the stack.
]#
[
  p.[Unexpectedly NIL pattern]a.!
  [p.._ [                                            [ [Pattern is link.]WL ]#
      s. i. p. ".o.!
    ]?                                              [ [Pattern is value.]WL ]#
      p..                                           [ [Pattern char = ]W "W ]#
      i.. [                                           [, Input char = ]W "W ]#
      = e:
      [                                                [, match: ]W e.`0+WL ]#
                                                         [ [After match ]WS ]#
      [e. [i.,i:]? ]!
      [                                             [After input advance]WS ]#
                           [ [Input is now ]W i.  [" [.]? #[nil]]! W [, ]WS ]#
      [ s. e. =                                         [ [s=e: ]W "`0+WL   ]#
        p.,                                             [ [p.,: ]W "~~`0+WL ]#
        &                                               [ [&: ]W   "`0+WL   ]#
        [p.,p:]? b.!
      ]!
  ]!
] m:

[BackTrack ( NIL | prevseq previnp prevpat -- )]#
[                                                   [ [Backtrack entry, ]WS ]#
  "_[Backtrack: expected link on top of stack.]a.!
  [ " ~ [                                           [ [Pattern complete.]WL ]#
          # e. 0p:
        ]?
    p:                       [[Backtrack - pattern updated to ']W p.W ['.]WL]#
                                                       [ [Backtrack (2) ]WS ]#
    [ e. [#]? i: ]!
                                                       [ [Backtrack (3) ]WS ]#
    "_~[Backtrack Expected save seq flag on top of stack.]a.!
    s:
                 [[Backtrack (4) p: ]W p.W [, i: ]W i.W [, s: ]W s.W [, ]W S]#
    [ e. s. =[ p.,p: ]? b.! ]!
                 [[Backtrack (5) p: ]W p.W [, i: ]W i.W [, s: ]W s.W [, ]W S]#
  ]!
] b:

[Testmatch (expectation input pattern --)]#
[
  L[Testing match, input: ]W %"W % [, pattern: ]W "W L
  o.!  i:
                                                                        [ S ]#
  N
  [                      [ [Step, input=']W i.W [', pattern=']W p.W [', ]WS ]#
    m.!
    p.`@?
  ]!

                                                       [ [Match exited, ]WS ]#
  [Result:   ]W [ "_[[unexpected link on top of stack.]WL #]? `0+WL]!
  [Expected: ]W [ "_[[unexpected link on top of stack.]WL #]? `0+WL]!
] t:

  1 [Fred] ['Fred] t.!
  0 [Fred] ['Bert] t.!
  0 [Frip] ['Fred] t.!
  1 [t]    [/tuv] t.!
  1 [t]    [/rst] t.!
  0 [t]    [/abc] t.!
  1 [test] ['te['s]t] t.!
  1 [fred] [/['bert]['fred]['harry]] t.!
  1 [fred] ['fr[/aeiou]d] t.!
