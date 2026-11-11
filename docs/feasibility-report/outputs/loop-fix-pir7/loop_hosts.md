EBs announced in the window 252, slots 1,899,923 to 1,904,652; validated by PIR7 218, by PIR9 220 (grafana/archive/loki/loop-fix-pir7).

| host, 2026-11-08 23:45 to 11-09 01:04 UTC | EBs validated | apply cost per transaction | reapply cost per transaction | EBs applying 500 or more with few reapplies: validation per applied transaction, p50 |
|---|---:|---:|---:|---:|
| the changed host | 218 | 0.30 ms | 0.17 ms | 0.35 ms |
| the control | 220 | 1.66 ms | 0.19 ms | 1.40 ms |

| transactions applied in the EB | the changed host: EBs | validation p50 / p90 | per applied transaction, p50 | the control: EBs | validation p50 / p90 | per applied transaction, p50 |
|---|---:|---:|---:|---:|---:|---:|
| 100 to 500 | 42 | 0.18 / 0.50 s | 0.59 ms | 42 | 0.46 / 0.88 s | 1.78 ms |
| 500 to 1,000 | 28 | 0.38 / 0.84 s | 0.55 ms | 27 | 1.30 / 1.91 s | 1.77 ms |
| 1,000 to 2,000 | 22 | 0.64 / 1.00 s | 0.42 ms | 25 | 2.05 / 2.80 s | 1.53 ms |
| 2,000 and up | 19 | 1.11 / 1.34 s | 0.38 ms | 13 | 4.17 / 6.95 s | 1.72 ms |

the changed host (PIR7): votes scheduled 219, cast 217, too late 2 (closure after the deadline or never: 1, at 15.4 s; validation past the deadline: 1, closures by 7.0 s), other reasons 0; largest validation 1.73 s on an EB of 6,997 transactions (2,787 applied).
the control (PIR9): votes scheduled 221, cast 211, too late 10 (closure after the deadline or never: 1, at 15.4 s; validation past the deadline: 9, closures by 5.8 s), other reasons 0; largest validation 7.76 s on an EB of 3,769 transactions (3,316 applied).
