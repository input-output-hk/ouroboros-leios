db-analyser \
  --verbose \
  --db /scratch/iohk/networks/mainnet/node.db/ \
  --analyse-from 159210863 \
  --num-blocks-to-process 1000 \
  --benchmark-ledger-ops \
    --out-file ledger-ops-cost.csv \
  cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json



nix build 'github:IntersectMBO/ouroboros-consensus/release-ouroboros-consensus-diffusion-0.20.0.0#db-analyser'

# Store ledger state for epoch 350
db-analyser \
  --db /scratch/iohk/networks/mainnet/node.db/ \
  --store-ledger 65836843 \
  cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json

db-analyser \
  --db /scratch/iohk/networks/mainnet/node.db/ \
  --analyse-from 65836843 \
  --num-blocks-to-process 1000 \
  --benchmark-ledger-ops \
    --out-file ledger-ops.csv \
  cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json


db-analyser --verbose --db /scratch/iohk/networks/mainnet/node.db/ --analyse-from 65836843 --num-blocks-to-process 1 --benchmark-ledger-ops --out-file wo-reapply.csv cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json

db-analyser --verbose --db /scratch/iohk/networks/mainnet/node.db/ --analyse-from 65836843 --num-blocks-to-process 1 --benchmark-ledger-ops --out-file w-reapply.csv --reapply cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json

db-analyser \
  --verbose \
  --db /scratch/iohk/networks/mainnet/node.db/ \
  --analyse-from 65836843 \
  --benchmark-ledger-ops \
    --out-file ledger-ops.tsv \
  cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json

db-analyser \
  --db /scratch/iohk/networks/mainnet/node.db/ \
  --store-ledger 134028814 \
  cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json

db-analyser \
  --db /scratch/iohk/networks/mainnet/node.db/ \
  --analyse-from 134028814 \
  --benchmark-ledger-ops \
    --out-file ledger-ops.csv \
  cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json

db-analyser \
  --db /scratch/iohk/networks/mainnet/node.db/ \
  --analyse-from 134028814 \
  --benchmark-ledger-ops \
    --out-file ledger-ops-reapply.csv \
  --reapply \
  cardano --config /scratch/iohk/networks/mainnet/analysis/config/config.json
