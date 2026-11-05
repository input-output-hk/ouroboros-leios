range 2026-10-24T12:00:00Z .. 2026-10-26T13:00:00Z, 25 windows from windows-f2-high.txt, 25 h
RBs 3536 (observed 1 RB / 25.5 s; nominal f = 0.05), G = 14 slots, EBs announced 3473, eligible 2128, certified 1033
caps: references 308,000 B, payload 2,000,000 B (committee.sqlite, epoch 26); full EB = reference list >= 224 KB (99 % of the binding capacity)

level                   tx KB/s   TPS@318B   assumption
parameter ceiling         53.53          -   payload cap 2 MB, f = 0.05 (1 RB / 20 s), p = (1-f)^(G-1) = 0.513
workload ceiling          53.53      168.2   payload cap binds at 318 B/tx (measured): E = 2000 KB, 6,284 txs
observed spacing          49.52      155.6   observed 1 RB / 25.5 s and p observed = 0.613
voting-adjusted, mix      25.86       81.3   x s_all = 0.485 (certified/eligible of all EBs; certified closure p90 = 1,733 KB, 5,446 txs)
voting-adjusted, full     10.06       31.6   x s_full = 0.142 (certified/eligible of full EBs; cap at sustained full load)
load-adjusted             16.01       50.3   x s_all = 0.485 (actual mix); RBs announcing 0.982; EB payload 0.599 of its cap; plain RB 0.903 of the block limit
measured                  12.05       38.0   

written to ladder.jsonl (1 range(s))
