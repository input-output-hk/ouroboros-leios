|           what            |                 kind                 | rbs  | adoptions | delay_p50 | delay_p90 | within_1s_pct | within_1_5s_pct | within_2s_pct |
|---------------------------|--------------------------------------|-----:|----------:|----------:|----------:|--------------:|----------------:|--------------:|
| adoption delay by RB kind | c0 certifies, closure under 300 kB   | 14   | 714       | 0.97      | 1.25      | 53.8          | 99.6            | 99.6          |
| adoption delay by RB kind | c1 certifies, closure 300-500 kB     | 99   | 5049      | 1.14      | 1.45      | 28.5          | 97.9            | 99.1          |
| adoption delay by RB kind | c2 certifies, closure 500 kB to 1 MB | 1015 | 51765     | 1.2       | 1.52      | 8.8           | 86.7            | 97.1          |
| adoption delay by RB kind | p0 plain RB, small                   | 35   | 1785      | 0.15      | 0.48      | 100.0         | 100.0           | 100.0         |
| adoption delay by RB kind | p1 plain RB, full (80 kB and up)     | 1916 | 97685     | 1.13      | 1.84      | 31.2          | 68.5            | 94.9          |
|      what      |   reason    |  n   |
|----------------|-------------|-----:|
| switch reasons | VRFTiebreak | 5437 |
| switch reasons | Longer      | 309  |
|    what    | leader_slots | forged | adopted | didnt_adopt | leader_slots_not_forged |
|------------|-------------:|-------:|--------:|------------:|------------------------:|
| leadership | 3291         | 3291   | 3237    | 54          | 0                       |
|            what             | events | nodes | rbs | gap_min | gap_avg |
|-----------------------------|-------:|------:|----:|--------:|--------:|
| LeiosCertRbWithoutCandidate | 506    | 51    | 60  | 14      | 35.6    |
