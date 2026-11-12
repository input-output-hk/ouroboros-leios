range 2026-10-21T16:39:00Z .. 2026-10-22T09:50:00Z, whole range
RBs 2966 (observed 1 RB / 20.8 s; nominal f = 0.05), G = 14 slots, EBs announced 2944, eligible 1570, certified 820
caps: references 100,000 B, payload 1,000,000 B (from flags); full EB = reference list >= 98 KB (99 % of the binding capacity); reference width 37.00 B per transaction, measured on the certified EBs

level                   tx KB/s   TPS@374B   assumption
parameter ceiling         27.86          -   payload cap 1 MB, f = 0.05 (1 RB / 20 s), p = (1-f)^(G-1) = 0.513
workload ceiling          27.86       74.5   payload cap binds at 374 B/tx (measured): E = 1000 KB, 2,674 txs
observed spacing          27.61       73.8   observed 1 RB / 20.8 s and p observed = 0.533
voting-adjusted, full     16.90       45.2   x s_full = 0.540 (certified/eligible of full EBs; cap at sustained full load)
load-adjusted             15.53       41.5   x s_all = 0.522 (actual mix); RBs announcing 0.993; EB payload 0.940 of its cap; plain RB 0.980 of the block limit
measured                  15.46       41.3   

written to ladder.jsonl (1 range(s))
