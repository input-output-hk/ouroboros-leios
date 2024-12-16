# This script reads a JSON file from the Haskell simulation of Praos
# and extracts the inter-node latencies from the network graph definition.

# usage: jq -srf latencies.jq <json_file>

# half of the latencies are "near" (and thus quick) the other half are "far" (and thus slower)
[.[]|.[1]] | sort |
["near", [.[range(0;length/2)]]], ["far", [.[range(length/2;length)]]] |
.[0] as $name |
.[1] |
length as $l | . as $v |
range(1;10) | . as $mult |
[
    foreach $v[] as $i (0;
        .+1;
        if .%100==0 or .==$l then [$i*$mult, ./$l] else null end) |
    select(.)
] |
reverse |
[
  # keep only the last value for each time
  foreach .[] as $p ([0]; [$p[0], .[0]]; if .[0] != .[1] then "("+($p[0]|tostring)+", "+($p[1]|tostring)+")" else null end) |
  select(type == "string")
] |
reverse |
"send" + ($mult|tostring) + $name + " := CDF[" + join(", ") + "]"
