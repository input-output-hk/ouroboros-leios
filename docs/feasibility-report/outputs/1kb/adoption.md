|             what              | leader_slots | forged | leader_slots_not_forged | hosts |
|-------------------------------|-------------:|-------:|------------------------:|------:|
| leadership of reporting hosts | 168          | 168    | 0                       | 13    |
| period |             kind              | rbs | node_adoptions | delay_p50 | delay_p90 | within_1s_pct | within_2s_pct |
|--------|-------------------------------|----:|---------------:|----------:|----------:|--------------:|--------------:|
| loaded | a certifies, closure < 0.5 MB | 16  | 1285           | 0.39      | 1.11      | 84.1          | 99.8          |
| loaded | b certifies, closure 0.5-1 MB | 7   | 558            | 0.59      | 1.29      | 76.9          | 98.6          |
| loaded | c certifies, closure 1-1.5 MB | 14  | 1133           | 0.43      | 0.85      | 95.5          | 99.5          |
| loaded | d certifies, closure 1.5-2 MB | 122 | 9858           | 0.62      | 1.55      | 74.9          | 94.9          |
| loaded | e plain RB, < 80 kB           | 34  | 2712           | 0.47      | 1.49      | 76.5          | 94.5          |
| loaded | f plain RB, 80-88 kB          | 438 | 34768          | 0.62      | 2.12      | 73.5          | 89.4          |
