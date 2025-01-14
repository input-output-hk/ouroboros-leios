# attempt to find triangles in the network graph produced by the Haskell simulation of Praos

[.[]|.[0]] as $links |
range(1000) |
. as $i |
[$i,
  (
    [$links[]|select(contains([$i]))|.[]|select(. != $i)] | unique |
    . as $peers |
    length as $l |
    # count the number of pairs of peers that are connected
    reduce range($l) as $j (0; . + (reduce range($j + 1;$l) as $k (0; . + (if ($links[]|contains([[$peers[$j],$peers[$k]]])) then 0 else 1 end)))) |
    [$l, .]
  )
]
