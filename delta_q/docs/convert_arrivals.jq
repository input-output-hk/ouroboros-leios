def format: . * 10000 | round / 10000 | tostring;

.stable_chain_hashes as $stable |
.entries[] |
.created as $t0 | .hash as $hash |
.arrivals | length as $l |
select($l == 1000 and ($stable|contains([$hash]))) |
sort |
[
  foreach .[]
  as $p 
  (
    0;
    .+1;
    [(($p-$t0)|format), (./$l|format)]
  )
] |
reverse |
[
  # keep only the last value for each time
  foreach .[] as $p ([0]; [$p[0], .[0]]; if .[0] != .[1] then "("+$p[0]+", "+$p[1]+")" else null end) |
  select(type == "string")
] |
reverse
|
"CDF[" + join(", ") + "]"
