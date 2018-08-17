' 3}
'[Bootstrapping ...]3}
'[-----------------]3}


'[0{ % 1} 91+=~?[x!]]x:
x!
2}


'[0{ % 1} 91+=~]   '[fn that echos a char and returns if it was LF]#




'[
  p.._?[ '[Pattern entry is link]#
    s. i. p.  '[Push sequence flag, input position and pattern position on local stack]#
    p.. %,p! .''=s!  '[Initialise match in nested list]#
  ][     '[Pattern entry is value]#
    p.. i.. =
    %?[i.,i.:]
    % s.= p., & ?[#p.,p:]\[b!]
  ]
]m:
