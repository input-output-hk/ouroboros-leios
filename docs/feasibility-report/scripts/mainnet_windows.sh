#!/bin/sh
# The mainnet congestion windows of report section 1 (Praos under load), one
# block of mainnet_praos.py output per window, written to stdout as Markdown.
# Data: $LEIOS_MAINNET (default ../mainnet next to the scripts) holding
# blocks_<epoch>.jsonl and params_<epoch>.json from mainnet_blocks.py for
# epochs 316, 453, 507, 525, 660 and 661. "Full" = 90 % of the epoch's
# max_block_size (a block stops when the next transaction does not fit).
#
#   LEIOS_MAINNET=/path/to/mainnet sh mainnet_windows.sh > MAINNET-WINDOWS.md
set -e
P="python3 $(dirname "$0")/mainnet_praos.py"
echo "# Mainnet congestion windows, regenerated $(date -u +%Y-%m-%d) with mainnet_praos.py --full 0.9 --top 0"
echo; echo "## epoch 316, 2022-01-21 00:00 to 01-23 06:00 UTC (SundaeSwap launch)"
$P 316 --from 2022-01-21T00:00:00 --to 2022-01-23T06:00:00 --full 0.9 --top 0
echo; echo "## epoch 453, 2023-12-08 06:00 to 12-09 18:00 UTC (memecoin minting wave)"
$P 453 --from 2023-12-08T06:00:00 --to 2023-12-09T18:00:00 --full 0.9 --top 0
echo; echo "## epoch 507, 2024-09-05 12:00 to 09-06 00:00 UTC (Snek.fun launch)"
$P 507 --from 2024-09-05T12:00:00 --to 2024-09-06T00:00:00 --full 0.9 --top 0
echo; echo "## epoch 525, 2024-12-02 18:00 to 12-03 00:00 UTC (bull-run activity)"
$P 525 --from 2024-12-02T18:00:00 --to 2024-12-03T00:00:00 --full 0.9 --top 0
echo; echo "## epoch 660, 2026-10-08 06:00 to 18:00 UTC (Hosky spam campaign)"
$P 660 --from 2026-10-08T06:00:00 --to 2026-10-08T18:00:00 --full 0.9 --top 0
echo; echo "## epoch 661, whole epoch (normal operation)"
$P 661 --full 0.9 --top 0
