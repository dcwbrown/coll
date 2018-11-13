C[ADAPT testing.]WL

[Locals test.]WL
1 2 3 4
4(
   aWL bWL cWL dWL

   [---]WL

   [First string] [Second string] [Third string]
   3( aWL bWL cWL )

   [---]WL

   aWL bWL cWL dWL

   [---]WL
)

[Variable store test.]WL



[s: Similar (l1 l2 -- l1' l2' length)]#

[ 0`c
  2([
    a_ b_ &~ []?      [Exit if either is not a link.]#
    a. b. =~ []?      [Exit if they reference different values.]#
    a,`a  b,`b  c1+`c
    1@?
  ]! a b c)
] `s

[alpha] [alpha] SL s! SL ###
[alpha] [algol] SL s! SL ###
[alpha] [beta]  SL s! SL ###


[m: Match (key pattern -- key' pattern' length)]#

[ Match key against pattern.
  Pattern is a string follwed by a set of links to nested patterns.

  match(keyp patternp)
    similar(keyp patternp length)
    if length>0 then
      subpattern := patternp.next
      subkey := keyp.next
      bestlength := 0
      while subpattern is link do
        similar(subkey, subpattern.link, sublength)
        if sublength>bestlength then
          keyp := subkey  patternp := subpattern  bestlength := sublength
        end
        subpattern := subpattern.next
      end
      inc(length, bestlength)
    end
  end match
]#


E

[Individual function tests.]#


[Match test (string pattern)]#
[ \p: \c: 0\t: 01-
  [Before begin-match]d!

  L[---]WL
  [p ]W p S
  [. ]W . S
  [, ]W , S #

  s!
  [After begin-match]d!

  S
  [ m! [After match]d! " 2<@? 2-]!
  [Match test complete, ]W S # L
]Ty



[
[sequin] [ sequin]   y!
[sequin] [ sequence] y!
[fred]   [ sequence] y!
[t]      [/tuv]      y!
[u]      [/tuv]      y!
[v]      [/tuv]      y!
[w]      [/tuv]      y!
[test]   [ te[ s]t]  y!
[fred]   [/['bert]['fred]['harry]] y!
[fred]   ['fr[/aeiou]d] y!
]#

[tes]   [ te[ s]t]  y!
