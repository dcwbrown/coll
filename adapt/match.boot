L
[Matching ...]WL
[------------]WL


[Variables:
  p - current position in pattern
  c - current position in input
  t - type of current pattern

 Functions:
  b - beginning of pattern
  m - match one pattern position
  i - handle int in pattern
  l - handle link in pattern
  a - advance pattern
  s - succeeding backtrack
  f - failing backtrack
]#


[p.. `/=t: p.,p:]b:

[p.._ [l.!]? i.!]m:

[ p.. c.. =        [Compare pattern and input]#
  ["[c.,c:]?]!     [Advance input if match]#
  t.= [x.!]? a.!   [Backtrack or advance pattern]#
]i:

[ "0< [#03- t.+]?    [If finished leave TOS as -2/-3]#
  t.[s.!]?f.!
]x:

[ p..           [Push link to current position in pattern]#
  [t.[c.]?]!    [Push input position when alt pattern]#
  t.            [Push type (seq/alt)]#
  p...p:        [Position to start of nested list]#
  b.!           [Process beginning of pattern]#
]l:

[ p.," [p:]? #     [If there's a next, just follow it]#
  t. [f.!]? s.!    [backtrack alt->failing, seq->succeeding]#
]a:

["0< [#02-]?       [If finished leave TOS as -2]#
 "t:               [Restore enclosing pattern type]#
 [
  [Successful backtrack to alt pattern]#
  #      [Drop saved input position]#
  p:     [Restore position in enclosing pattern]
  s.!    [Continue successful backtrack in enclosing pattern]#
 ]?
  [Successful backtrack to seq pattern]#
  p:     [Restore position in enclosing pattern]
  a.!    [Advance in enclosing pattern]#
]s:

["0< [#03-]?      [If finished leave TOS as -3]#
 "t:              [Restore enclosing pattern type]#
 [
  [Successful backtrack to alt pattern]#
  c:     [Restore saved input position]#
  p:     [Restore position in enclosing pattern]
  a.!    [Advance in enclosing pattern]#
 ]?
  [Successful backtrack to seq pattern]#
  #      [Drop position in enclosing pattern]
  f.!    [Continue failing backtrack in enclosing pattern]#
]f:


[Individual function tests.]#


[Debug dump match status.]#
[W  [. p ']W p.W [', c ']W c.W [', t ]W t.`0+W [, TOS ]W "W [.]WL]d:

[Match test. (pattern string)]#
[ c: p: 0t: 01-
  [Before begin-match]d.!
  b.!
  [After begin-match]d.!
  [ m.! [After match]d.! " 1+0<~@? 3+]!
  [Match test complete, ]W S # L
]y:

[ sequin] [sequin] y.!
[ sequence] [sequin] y.!



[
  1 [Fred] ['Fred] t.!
  0 [Fred] ['Bert] t.!
  0 [Frip] ['Fred] t.!
  1 [t]    [/tuv] t.!
  1 [t]    [/rst] t.!
  0 [t]    [/abc] t.!
  1 [test] ['te['s]t] t.!
  1 [fred] [/['bert]['fred]['harry]] t.!
  1 [fred] ['fr[/aeiou]d] t.!
]#