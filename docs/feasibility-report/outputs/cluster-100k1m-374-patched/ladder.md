range 2026-11-09T16:45:00Z .. 2026-11-10T09:03:00Z, whole range
RBs 2954 (observed 1 RB / 19.9 s; nominal f = 0.05), G = 14 slots, EBs announced 2927, eligible 1446, certified 1434
caps: references 100,000 B, payload 1,000,000 B (from flags); full EB = reference list >= 95 KB (99 % of the binding capacity)

level                   tx KB/s   TPS@374B   assumption
parameter ceiling         27.86          -   payload cap 1 MB, f = 0.05 (1 RB / 20 s), p = (1-f)^(G-1) = 0.513
workload ceiling          27.86       74.5   payload cap binds at 374 B/tx (measured): E = 1000 KB, 2,674 txs
observed spacing          27.18       72.7   observed 1 RB / 19.9 s and p observed = 0.494
voting-adjusted, full     26.99       72.2   x s_full = 0.992 (certified/eligible of full EBs; cap at sustained full load)
load-adjusted             27.30       73.0   x s_all = 0.992 (actual mix); RBs announcing 0.991; EB payload 1.024 of its cap; plain RB 0.973 of the block limit
measured                  26.63       71.1   

written to ladder.jsonl (1 range(s))
