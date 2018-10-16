L
[Matching ...]WL
[------------]WL


[ Functions:
    s - Setup match
    m - match one pattern position
    i - handle int in pattern
    l - handle link in pattern
    a - advance pattern
    b - backtrack
    e - succeeding backtrack
    f - failing backtrack

  Variables:
    p - current position in pattern
    c - current position in input
    t - type of current pattern

  Common state on stack:
    if no prev (enclosing) pattern, -1
    else
      if prev pattern is sequence:      prev-pat-pos prev-pat-type
      if prev pattern is alternatives:  prev-pat-pos prev-input-pos prev-pat-type
]#

[d: Debug dump match status.]#
[W  [. c ']W c.W [', p ']W p.W [', t ]W t.`0+W [, TOS ]W "W [.]WL]d:


[s: setup match
    entry  p -> first (type) char of pattern
           c -> first char of key string 
    exit   p    advanced over type char
           t    false iff sequence pattern
                true iff alternates pattern
]#
[p.. `/=t: p.,p:]s:

[m: match step]#
[p.._ [l.!]? i.!]m:

[i: match integer value]#
[ [Match integer value. ]W
  p.. c.. =           [Compare pattern and input]#
  ["[[matched]]?[mismatched]]!WL
  ["[c.,c:]?]!        [Advance input if match]#
  t.= [t. b.!]? a.!   [Backtrack or advance pattern]#
]i:

[l: match link value]#
[ [Match link value. ]W S
  p.            [Push link to current position in pattern]#
  [t.[c.]?]!    [Push input position when alt pattern]#
  t.            [Push type (seq/alt)]#
  p..p:         [Position to start of nested list]#
  s.!           [Process beginning of pattern]#
]l:

[a: advance pattern]#
[ [Advance.]WL
  p.," [p:]? #  [If there's a next, just follow it]#
  t.~ b.!       [If no next, EOL => success for seq, failure for alt]#
]a:

[ Backtrack:
  Successful backtrack is when reaching end of sequence
                       or when value matches in alternatives
  Failing backtrack    is when reaching end of alternatives
                       or when value doesn't match in sequence 
]#

[ b: backtrack pattern ( .. (prev-pat-type|-1) success --) ]#
[ 
  [Backtrack 1]d.! [t ]W tW [ ]WS

  %"t:        [Restore enclosing pattern type]#

  [Backtrack 2 t ]W tW [ ]WS

  0< [2+]?    [If finished leave TOS as 2 (fail) or 3 (success) ]#

  [Stack holds success, t holds prev pattern type.]#

  [Backtrack 3 t ]W tW [ ]WS

  [If prev pat was alternates, handle stacked input pos:
    success -> drop, fail -> restore.]#
  [t.[  "[%#]?%c:  ]?]! 

  [Backtrack 4 t ]W tW [ ]WS

  [If failing to seq pattern leave p untouched, so if 
   we backtrack all the way out we'll see how deep we got.
   In all other cases, restore it.]#
  ["t.|[%p:]?%#]!
  
  [Backtrack 5 t ]W tW [ ]WS

  [If successful backtrack to seq, or failing backtrack to 
    alt, advance pattern and exit.
    Otherwise continue backtracking.]#

  "t.=~[#a.!]? b.!

  [Backtrack 6 t ]W tW [ ]WS
]b:


[Individual function tests.]#


[Match test. (string pattern)]#
[ p: c: 0t: 01-
  [Before begin-match]d.!
  s.!
  [After begin-match]d.!
  [ m.! [After match]d.! " 2<@? 2-]!
  [Match test complete, ]W S # L
]y:



[
[sequin] [ sequin]   y.!
[sequin] [ sequence] y.!
[fred]   [ sequence] y.!
[t]      [/tuv]      y.!
[u]      [/tuv]      y.!
[v]      [/tuv]      y.!
[w]      [/tuv]      y.!
[test]   [ te[ s]t]  y.!
[fred]   [/['bert]['fred]['harry]] y.!
[fred]   ['fr[/aeiou]d] y.!
]#

[tes]   [ te[ s]t]  y.!
