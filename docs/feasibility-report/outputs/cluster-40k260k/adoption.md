|           what            |                kind                | rbs  | adoptions | delay_p50 | delay_p90 | within_1s_pct | within_1_5s_pct | within_2s_pct |
|---------------------------|------------------------------------|-----:|----------:|----------:|----------:|--------------:|----------------:|--------------:|
| adoption delay by RB kind | c0 certifies, closure under 300 kB | 1539 | 78488     | 0.92      | 1.21      | 61.3          | 98.2            | 98.7          |
| adoption delay by RB kind | p0 plain RB, small                 | 23   | 1173      | 0.16      | 0.45      | 100.0         | 100.0           | 100.0         |
| adoption delay by RB kind | p1 plain RB, full (80 kB and up)   | 1521 | 77571     | 1.03      | 1.7       | 46.0          | 80.8            | 99.0          |
|      what      |   reason    |  n   |
|----------------|-------------|-----:|
| switch reasons | VRFTiebreak | 3426 |
| switch reasons | Longer      | 110  |
|    what    | leader_slots | forged | adopted | didnt_adopt | leader_slots_not_forged |
|------------|-------------:|-------:|--------:|------------:|------------------------:|
| leadership | 3233         | 3233   | 3195    | 38          | 0                       |
|            what             | events | nodes | rbs | gap_min | gap_avg |
|-----------------------------|-------:|------:|----:|--------:|--------:|
| LeiosCertRbWithoutCandidate | 595    | 51    | 58  | 15      | 40.6    |
