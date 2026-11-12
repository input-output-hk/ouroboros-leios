range 2026-10-28T18:00:00Z .. 2026-10-29T01:00:00Z, 4 windows from windows-1kb.txt, 4 h
RBs 636 (observed 1 RB / 22.6 s; nominal f = 0.05), G = 14 slots, EBs announced 634, eligible 361, certified 164
caps: references 308,000 B, payload 2,000,000 B (committee.sqlite, epoch 43); full EB = reference list >= 90 KB (99 % of the binding capacity); reference width 36.78 B per transaction, measured on the certified EBs

level                   tx KB/s   TPS@810B   assumption
parameter ceiling         53.53          -   payload cap 2 MB, f = 0.05 (1 RB / 20 s), p = (1-f)^(G-1) = 0.513
workload ceiling          53.53       66.1   payload cap binds at 810 B/tx (measured): E = 2000 KB, 2,468 txs
observed spacing          52.01       64.2   observed 1 RB / 22.6 s and p observed = 0.569
voting-adjusted, mix      25.80       31.8   x s_all = 0.454 (certified/eligible of all EBs; certified closure p90 = 2,000 KB, 2,468 txs)
voting-adjusted, full     15.20       18.8   x s_full = 0.234 (certified/eligible of full EBs; cap at sustained full load)
load-adjusted             29.95       37.0   x s_all = 0.454 (actual mix); RBs announcing 0.997; EB payload 1.195 of its cap; plain RB 0.923 of the block limit
measured                  21.96       29.6   

written to ladder.jsonl (1 range(s))
