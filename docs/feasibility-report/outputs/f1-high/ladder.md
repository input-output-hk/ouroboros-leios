range 2026-10-21T12:00:00Z .. 2026-10-22T01:00:00Z, 3 windows from windows-f1-high.txt, 6 h
RBs 944 (observed 1 RB / 22.9 s; nominal f = 0.05), G = 14 slots, EBs announced 935, eligible 548, certified 531
caps: references 40,000 B, payload 260,000 B (committee.sqlite, epoch 14); full EB = reference list >= 36 KB (99 % of the binding capacity); reference width 36.14 B per transaction, measured on the certified EBs

level                   tx KB/s   TPS@257B   assumption
parameter ceiling          8.87          -   payload cap 0.26 MB, f = 0.05 (1 RB / 20 s), p = (1-f)^(G-1) = 0.513
workload ceiling           8.87       34.5   payload cap binds at 257 B/tx (measured): E = 260 KB, 1,012 txs
observed spacing           8.29       32.3   observed 1 RB / 22.9 s and p observed = 0.586
voting-adjusted, full      8.18       31.8   x s_full = 0.976 (certified/eligible of full EBs; cap at sustained full load)
load-adjusted              7.17       27.9   x s_all = 0.969 (actual mix); RBs announcing 0.990; EB payload 0.899 of its cap; plain RB 0.822 of the block limit
measured                   7.17       28.1   

written to ladder.jsonl (1 range(s))
