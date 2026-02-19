#!/usr/bin/env bash
# Validate simulator against Brian Bush's analytical predictions
#
# Theory (from post-cip/mempool-model/ReadMe.md):
#   p_poison ≈ 1 - (1 - p_adv)^(λ-1)   for no-delay (unbiased competition)
#   p_poison ≈ p_adv                      for substantial delay (2ms)
#
# Where λ = log_k(N) ≈ 3.074 at N=10000, k=20
# So the no-delay slope ≈ λ-1 ≈ 2.074

set -eo pipefail
cd "$(dirname "$0")/.."

NODES=10000
DEGREE=20
TX_COUNT=500        # enough for statistical stability
TX_DURATION=100     # inject over 100s
SLOTS=0             # NO blocks — measure pure diffusion mempool state

echo "# Validate sim vs Brian's analytical model"
echo "# N=$NODES k=$DEGREE lambda=log_${DEGREE}($NODES)"
echo "# Theory: no-delay slope = lambda-1 ≈ 2.074, delay slope = 1"
echo "#"
echo "nodes,degree,adversaries,p_adv,delay,p_poison,theory_no_delay,theory_delay,avg_reach,front_run_rate,blocks"

for ADVERSARIES in 0 100 200 400 600 800 1000; do
  for DELAY in 0.0 0.002; do
    OUTPUT=$(npx tsx src/cli.ts \
      --nodes $NODES \
      --degree $DEGREE \
      --adversaries $ADVERSARIES \
      --adversary-degree $DEGREE \
      --adversary-delay $DELAY \
      --tx-count $TX_COUNT \
      --tx-duration $TX_DURATION \
      --tx-size-min 1500 --tx-size-max 1500 \
      --slot-duration 20 \
      --slots $SLOTS \
      --log-level info \
      --log-target pino/file 2>&1)

    # Extract poisoning analysis
    POISON=$(echo "$OUTPUT" | grep '"poisoning analysis"' | tail -1)
    BLOCKS_STATS=$(echo "$OUTPUT" | grep '"block statistics"' | tail -1)

    P_POISON=$(echo "$POISON" | jq -r '.p_poison // 0')
    THEORY_ND=$(echo "$POISON" | jq -r '.theory_no_delay // 0')
    THEORY_D=$(echo "$POISON" | jq -r '.theory_delay // 0')
    P_ADV=$(echo "$POISON" | jq -r '.p_adv // 0')
    AVG_REACH=$(echo "$POISON" | jq -r '.avg_reach // 0')

    if [ -n "$BLOCKS_STATS" ]; then
      FRONT_RUN=$(echo "$BLOCKS_STATS" | jq -r '.front_run_rate // 0')
      BLOCKS=$(echo "$BLOCKS_STATS" | jq -r '.blocks_produced // 0')
    else
      FRONT_RUN=0
      BLOCKS=0
    fi

    echo "$NODES,$DEGREE,$ADVERSARIES,$P_ADV,$DELAY,$P_POISON,$THEORY_ND,$THEORY_D,$AVG_REACH,$FRONT_RUN,$BLOCKS"
  done
done
