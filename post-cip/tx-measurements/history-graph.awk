#!/usr/bin/env -S gawk -f

BEGIN {
  FS = "\t"
  OFS = "\t"
}

FNR == 1 {
  print "utxo_id8", "tx_create_id", "tx_spend_id", "slots", "blocks"
}

FNR > 1 && $3 != "" {
  print substr($1, 0, 8) substr($1, 65), $2, $3, $5 - $4, $7 - $6
}
