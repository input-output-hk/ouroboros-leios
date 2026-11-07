|             what              | on_chain_no_fork | on_chain_first_certifies | on_chain_first_plain | forked | forked_first_rb_lost | forked_second_rb_lost | forked_first_certifies | forked_first_plain | orphan_size_unknown | fork_share_pct |
|-------------------------------|-----------------:|-------------------------:|---------------------:|-------:|---------------------:|----------------------:|-----------------------:|-------------------:|--------------------:|---------------:|
| consecutive-slot leader pairs | 20               | 4                        | 16                   | 5      | 4                    | 1                     | 1                      | 4                  | 0                   | 20.0           |
|                              kind                               | forks | orphan_certifies | competitor_certifies |
|-----------------------------------------------------------------|------:|-----------------:|---------------------:|
| a orphan 2+ slots before the competitor                         | 1     | 0                | 0                    |
| b orphan one slot before (consecutive-slot pair, first RB lost) | 4     | 1                | 1                    |
| c same slot (slot battle)                                       | 9     | 3                | 3                    |
| d orphan one slot after (consecutive-slot pair, second RB lost) | 1     | 0                | 0                    |
