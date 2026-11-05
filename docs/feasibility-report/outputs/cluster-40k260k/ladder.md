range 2026-10-17T22:01:00Z .. 2026-10-18T15:40:00Z, whole range
RBs 3062 (observed 1 RB / 20.7 s; nominal f = 0.05), G = 15 slots, EBs announced 3059, eligible 1547, certified 1539
caps: references 40,000 B, payload 260,000 B (from flags); full EB = reference list >= 40 KB (99 % of the binding capacity)

level                   tx KB/s   TPS@200B   assumption
parameter ceiling          8.65          -   payload cap 0.26 MB, f = 0.05 (1 RB / 20 s), p = (1-f)^(G-1) = 0.488
workload ceiling           7.73       38.6   reference cap binds at 200 B/tx (measured): E = 222 KB, 1,111 txs
observed spacing           7.57       37.8   observed 1 RB / 20.7 s and p observed = 0.506
voting-adjusted, full      7.55       37.8   x s_full = 0.995 (certified/eligible of full EBs; cap at sustained full load)
load-adjusted              7.50       37.5   x s_all = 0.995 (actual mix); RBs announcing 0.999; EB payload 0.999 of its cap; plain RB 0.981 of the block limit
measured                   7.50       37.4   

written to ladder.jsonl (1 range(s))
