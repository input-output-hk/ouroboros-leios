|             what              | on_chain_no_fork | on_chain_first_certifies | on_chain_first_plain | forked | forked_first_rb_lost | forked_second_rb_lost | forked_first_certifies | forked_first_plain | orphan_size_unknown | fork_share_pct |
|-------------------------------|-----------------:|-------------------------:|---------------------:|-------:|---------------------:|----------------------:|-----------------------:|-------------------:|--------------------:|---------------:|
| consecutive-slot leader pairs | 26               | 9                        | 17                   | 5      | 5                    | 0                     | 1                      | 4                  | 0                   | 16.1           |
|                              kind                               | forks | orphan_certifies | competitor_certifies |
|-----------------------------------------------------------------|------:|-----------------:|---------------------:|
| a orphan 2+ slots before the competitor                         | 2     | 1                | 1                    |
| b orphan one slot before (consecutive-slot pair, first RB lost) | 5     | 1                | 1                    |
| c same slot (slot battle)                                       | 16    | 11               | 11                   |
