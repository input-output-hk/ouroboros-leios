|             what              | leader_slots | forged | leader_slots_not_forged | hosts |
|-------------------------------|-------------:|-------:|------------------------:|------:|
| leadership of reporting hosts | 1185         | 1185   | 0                       | 13    |
| period |             kind              | rbs  | node_adoptions | delay_p50 | delay_p90 | within_1s_pct | within_2s_pct |
|--------|-------------------------------|-----:|---------------:|----------:|----------:|--------------:|--------------:|
| loaded | a certifies, closure < 0.5 MB | 319  | 22610          | 1.03      | 1.44      | 45.6          | 97.8          |
| loaded | b certifies, closure 0.5-1 MB | 342  | 24050          | 1.26      | 1.78      | 17.4          | 94.5          |
| loaded | c certifies, closure 1-1.5 MB | 179  | 12741          | 1.41      | 2.12      | 8.0           | 87.0          |
| loaded | d certifies, closure 1.5-2 MB | 161  | 11189          | 1.58      | 2.45      | 3.2           | 77.4          |
| loaded | e plain RB, < 80 kB           | 221  | 14617          | 0.99      | 4.49      | 50.9          | 80.9          |
| loaded | f plain RB, 80-88 kB          | 2209 | 153346         | 1.17      | 2.51      | 30.2          | 86.0          |
