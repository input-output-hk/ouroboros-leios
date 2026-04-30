#!/bin/bash
# Check sim-cli + trace-processor progress and report results if done
running=0
while IFS= read -r line; do
  pid=$(echo "$line" | awk '{print $1}')
  etime=$(echo "$line" | awk '{print $2}')
  rss=$(echo "$line" | awk '{printf "%.1f", $3/1024/1024}')
  who=$(echo "$line" | awk '{print $4}' | sed 's|.*/||')
  echo "$who PID=$pid elapsed=$etime RSS=${rss}GB"
  running=$((running + 1))
done < <(ps -eo pid,etime,rss,args 2>/dev/null | grep -E "sim-cli|leios-trace-processor|pigz -p 3 -9f" | grep -v grep)

# Check sweep logs
for log in /tmp/seed*-sweep.log /tmp/overnight-*.log; do
  [ -f "$log" ] || continue
  name=$(basename "$log")
  echo ""
  echo "=== $name ==="
  tail -10 "$log" 2>/dev/null
  if grep -q "All voting mode runs complete\|All overnight runs complete" "$log" 2>/dev/null; then
    echo "*** COMPLETE ***"
  fi
done

if [ "$running" -eq 0 ]; then
  echo ""
  echo "NO SIM OR TRACE PROCESSOR RUNNING"
fi
