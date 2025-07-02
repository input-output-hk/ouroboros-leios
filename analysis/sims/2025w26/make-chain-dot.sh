#!/usr/bin/env nix-shell
#!nix-shell -i bash -p gnugrep jq graphviz

zcat "$1" \
| grep RBGenerated \
| jq -r '
  select(.time_s <= 900 and .message.type == "RBGenerated")
  | "\"" + .message.id + "\" -> \"" + (if .message.parent then .message.parent.id else "GENESIS" end) + "\""
' \
> "$2.dot"

sed -e '1idigraph praos {' \
    -e '1irankdir=RL' \
    -e '1inode[shape=box]' \
    -e '$a}' \
    -i "$2.dot"

dot -Tpng -o "$2.png" "$2.dot"
