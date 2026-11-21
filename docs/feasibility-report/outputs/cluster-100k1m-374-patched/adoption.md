|           what            |                 kind                 | rbs  | adoptions | delay_p50 | delay_p90 | within_1s_pct | within_1_5s_pct | within_2s_pct |
|---------------------------|--------------------------------------|-----:|----------:|----------:|----------:|--------------:|----------------:|--------------:|
| adoption delay by RB kind | c1 certifies, closure 300-500 kB     | 1    | 51        | 0.37      | 0.54      | 100.0         | 100.0           | 100.0         |
| adoption delay by RB kind | c2 certifies, closure 500 kB to 1 MB | 1433 | 73071     | 0.51      | 0.75      | 98.7          | 99.2            | 99.3          |
| adoption delay by RB kind | p0 plain RB, small                   | 27   | 1377      | 0.16      | 0.39      | 100.0         | 100.0           | 100.0         |
| adoption delay by RB kind | p1 plain RB, full (80 kB and up)     | 1493 | 76111     | 0.59      | 1.17      | 75.1          | 95.3            | 98.3          |
|      what      |   reason    |  n   |
|----------------|-------------|-----:|
| switch reasons | VRFTiebreak | 2621 |
| switch reasons | Longer      | 51   |
|    what    | leader_slots | forged | adopted | didnt_adopt | leader_slots_not_forged |
|------------|-------------:|-------:|--------:|------------:|------------------------:|
| leadership | 3056         | 3056   | 3051    | 5           | 0                       |
|            what             | events | nodes | rbs | gap_min | gap_avg |
|-----------------------------|-------:|------:|----:|--------:|--------:|
| LeiosCertRbWithoutCandidate | 1074   | 51    | 60  | 14      | 32.1    |
