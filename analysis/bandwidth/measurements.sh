#!/usr/bin/env

jq -r '
  .intervals
| .[]
| .sum
| (input_filename | sub("^.*/(?<x>..)-(?<y>..)-(?<z>.)\\.json$"; "\(.x)\t\(.y)\t\(.z)"; "g"))+ "\t" + (.bits_per_second | tostring)
' 2025-09-04/*/*.json \
| sed -e '1isrc\tdst\ttrial\tbps' \
> measurements.tsv
