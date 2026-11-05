|             what              | leader_slots | forged | leader_slots_not_forged | hosts |
|-------------------------------|-------------:|-------:|------------------------:|------:|
| leadership of reporting hosts | 1185         | 1185   | 0                       | 13    |
| period |             kind              | rbs  | node_adoptions | delay_p50 | delay_p90 | within_1s_pct | within_2s_pct |
|--------|-------------------------------|-----:|---------------:|----------:|----------:|--------------:|--------------:|
| loaded | a certifies, closure < 0.5 MB | 317  | 22548          | 1.03      | 1.44      | 45.6          | 97.9          |
| loaded | b certifies, closure 0.5-1 MB | 334  | 23933          | 1.26      | 1.77      | 17.5          | 94.9          |
| loaded | c certifies, closure 1-1.5 MB | 175  | 12688          | 1.41      | 2.11      | 8.0           | 87.3          |
| loaded | d certifies, closure 1.5-2 MB | 156  | 11091          | 1.57      | 2.42      | 3.2           | 77.9          |
| loaded | e plain RB, < 80 kB           | 216  | 14448          | 0.98      | 4.4       | 51.5          | 81.5          |
| loaded | f plain RB, 80-88 kB          | 2185 | 152665         | 1.17      | 2.49      | 30.3          | 86.2          |
