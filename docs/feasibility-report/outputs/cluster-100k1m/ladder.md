range 2026-10-20T21:00:00Z .. 2026-10-21T14:47:00Z, whole range
RBs 3075 (observed 1 RB / 20.8 s; nominal f = 0.05), G = 14 slots, EBs announced 3044, eligible 1637, certified 1128
caps: references 100,000 B, payload 1,000,000 B (from flags); full EB = reference list >= 99 KB (99 % of the binding capacity); reference width 36.00 B per transaction, measured on the certified EBs

level                   tx KB/s   TPS@200B   assumption
parameter ceiling         27.86          -   payload cap 1 MB, f = 0.05 (1 RB / 20 s), p = (1-f)^(G-1) = 0.513
workload ceiling          16.45       82.3   reference cap binds at 200 B/tx (measured): E = 556 KB, 2,778 txs
observed spacing          16.36       81.8   observed 1 RB / 20.8 s and p observed = 0.538
voting-adjusted, full     12.61       63.1   x s_full = 0.689 (certified/eligible of full EBs; cap at sustained full load)
load-adjusted             12.18       60.9   x s_all = 0.689 (actual mix); RBs announcing 0.990; EB payload 0.973 of its cap; plain RB 0.967 of the block limit
measured                  12.17       60.7   

written to ladder.jsonl (1 range(s))
