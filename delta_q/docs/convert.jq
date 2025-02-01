# JQ script to convert JSONL file into a CDF
#
# the first line contains the start time
# each following line contains a JSON object with a `time` field

def format: . * 10000 | round / 10000 | tostring;

.[0] as $t0 | (length-1) as $l |
del(.[0]) |
sort_by(.time) |
[
  foreach .[]
  as $p 
  (
    0;
    .+1;
    [(($p.time-$t0)/1000000000|format), (./$l|format)]
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
