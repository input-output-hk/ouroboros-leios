#!/bin/bash
# Check sim-cli progress and report results if done
running=0
while IFS= read -r line; do
  pid=$(echo "$line" | awk '{print $1}')
  etime=$(echo "$line" | awk '{print $2}')
  rss=$(echo "$line" | awk '{printf "%.1f", $3/1024/1024}')
  echo "PID=$pid elapsed=$etime RSS=${rss}GB"
  running=$((running + 1))
done < <(ps -eo pid,etime,rss,args 2>/dev/null | grep sim-cli | grep -v grep)

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
  echo "NO SIM RUNNING"
fi
