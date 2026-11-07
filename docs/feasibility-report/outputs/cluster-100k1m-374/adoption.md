|           what            |                 kind                 | rbs  | adoptions | delay_p50 | delay_p90 | within_1s_pct | within_1_5s_pct | within_2s_pct |
|---------------------------|--------------------------------------|-----:|----------:|----------:|----------:|--------------:|----------------:|--------------:|
| adoption delay by RB kind | c0 certifies, closure under 300 kB   | 1    | 51        | 0.93      | 1.22      | 66.7          | 100.0           | 100.0         |
| adoption delay by RB kind | c1 certifies, closure 300-500 kB     | 9    | 459       | 1.17      | 1.32      | 40.5          | 93.5            | 96.3          |
| adoption delay by RB kind | c2 certifies, closure 500 kB to 1 MB | 810  | 41310     | 1.28      | 1.56      | 3.0           | 78.8            | 97.1          |
| adoption delay by RB kind | p0 plain RB, small                   | 23   | 1173      | 0.16      | 0.48      | 95.7          | 95.7            | 97.2          |
| adoption delay by RB kind | p1 plain RB, full (80 kB and up)     | 2125 | 108320    | 1.12      | 1.76      | 32.2          | 73.4            | 96.0          |
|      what      |   reason    |  n   |
|----------------|-------------|-----:|
| switch reasons | VRFTiebreak | 4919 |
| switch reasons | Longer      | 319  |
|    what    | leader_slots | forged | adopted | didnt_adopt | leader_slots_not_forged |
|------------|-------------:|-------:|--------:|------------:|------------------------:|
| leadership | 3175         | 3175   | 3114    | 61          | 0                       |
|            what             | events | nodes | rbs | gap_min | gap_avg |
|-----------------------------|-------:|------:|----:|--------:|--------:|
| LeiosCertRbWithoutCandidate | 412    | 51    | 51  | 14      | 33.1    |
