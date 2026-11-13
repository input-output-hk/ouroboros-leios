|             what              | on_chain_no_fork | on_chain_first_certifies | on_chain_first_plain | forked | forked_first_rb_lost | forked_second_rb_lost | forked_first_certifies | forked_first_plain | orphan_size_unknown | fork_share_pct |
|-------------------------------|-----------------:|-------------------------:|---------------------:|-------:|---------------------:|----------------------:|-----------------------:|-------------------:|--------------------:|---------------:|
| consecutive-slot leader pairs | 76               | 21                       | 55                   | 46     | 44                   | 2                     | 22                     | 24                 | 0                   | 37.7           |
|                              kind                               | forks | orphan_certifies | competitor_certifies |
|-----------------------------------------------------------------|------:|-----------------:|---------------------:|
| a orphan 2+ slots before the competitor                         | 11    | 4                | 2                    |
| b orphan one slot before (consecutive-slot pair, first RB lost) | 44    | 22               | 21                   |
| c same slot (slot battle)                                       | 38    | 7                | 6                    |
| d orphan one slot after (consecutive-slot pair, second RB lost) | 2     | 0                | 0                    |
| e orphan 2-5 slots after (competitor arrived late)              | 6     | 2                | 0                    |
