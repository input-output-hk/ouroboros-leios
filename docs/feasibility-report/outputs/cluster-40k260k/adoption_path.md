|           what            |                kind                 | node_rbs | nodes | closure_B_p50 | txs_p50 | dur_p50_s | dur_p90_s | us_per_tx |
|---------------------------|-------------------------------------|---------:|------:|--------------:|--------:|----------:|----------:|----------:|
| pop to adopted by RB kind | c0 certifying, closure under 0.2 MB | 153      | 51    | 151000.0      | 755.0   | 0.068     | 0.073     | 91.0      |
| pop to adopted by RB kind | c1 certifying, closure 0.2-0.5 MB   | 78335    | 51    | 222000.0      | 1110.0  | 0.104     | 0.126     | 94.0      |
| pop to adopted by RB kind | p0 plain, small                     | 1173     | 51    | NULL          | 0.0     | 0.002     | 0.003     | NULL      |
| pop to adopted by RB kind | p1 plain, full (80 kB+)             | 77571    | 51    | 222000.0      | 439.0   | 0.111     | 0.13      | 254.0     |
|                         what                         |               bin_a               |                bin_b                | us_per_tx | fixed_s |
|------------------------------------------------------|-----------------------------------|-------------------------------------|----------:|--------:|
| marginal us per closure tx (top two certifying bins) | c1 certifying, closure 0.2-0.5 MB | c0 certifying, closure under 0.2 MB | 100.0     | -0.007  |
|                    what                     | certifying_p50_s | plain_full_p50_s | closure_txs | us_per_tx |
|---------------------------------------------|-----------------:|-----------------:|------------:|----------:|
| certifying minus plain full, per closure tx | 0.104            | 0.111            | 1110.0      | -7.0      |
|           what           | node | rbs  | dur_p50_s | us_per_tx |
|--------------------------|-----:|-----:|----------:|----------:|
| per node, certifying RBs | 13   | 1539 | 0.099     | 89.0      |
| per node, certifying RBs | 5    | 1539 | 0.1       | 90.0      |
| per node, certifying RBs | 22   | 1539 | 0.1       | 90.0      |
| per node, certifying RBs | 29   | 1539 | 0.1       | 90.0      |
| per node, certifying RBs | 43   | 1539 | 0.1       | 90.0      |
| per node, certifying RBs | 49   | 1539 | 0.1       | 90.0      |
| per node, certifying RBs | 4    | 1539 | 0.101     | 91.0      |
| per node, certifying RBs | 17   | 1539 | 0.102     | 92.0      |
| per node, certifying RBs | 18   | 1539 | 0.102     | 92.0      |
| per node, certifying RBs | 24   | 1539 | 0.102     | 92.0      |
| per node, certifying RBs | 41   | 1539 | 0.102     | 92.0      |
| per node, certifying RBs | 42   | 1539 | 0.102     | 92.0      |
| per node, certifying RBs | 45   | 1539 | 0.102     | 92.0      |
| per node, certifying RBs | 46   | 1539 | 0.102     | 92.0      |
| per node, certifying RBs | 2    | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 3    | 1539 | 0.104     | 93.0      |
| per node, certifying RBs | 10   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 12   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 14   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 15   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 16   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 19   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 23   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 25   | 1539 | 0.104     | 93.0      |
| per node, certifying RBs | 27   | 1538 | 0.103     | 93.0      |
| per node, certifying RBs | 37   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 48   | 1539 | 0.103     | 93.0      |
| per node, certifying RBs | 0    | 1539 | 0.105     | 94.0      |
| per node, certifying RBs | 1    | 1539 | 0.105     | 94.0      |
| per node, certifying RBs | 6    | 1539 | 0.104     | 94.0      |
| per node, certifying RBs | 9    | 1539 | 0.104     | 94.0      |
| per node, certifying RBs | 11   | 1539 | 0.105     | 94.0      |
| per node, certifying RBs | 30   | 1539 | 0.104     | 94.0      |
| per node, certifying RBs | 36   | 1539 | 0.104     | 94.0      |
| per node, certifying RBs | 39   | 1539 | 0.104     | 94.0      |
| per node, certifying RBs | 20   | 1539 | 0.105     | 95.0      |
| per node, certifying RBs | 21   | 1539 | 0.105     | 95.0      |
| per node, certifying RBs | 33   | 1539 | 0.105     | 95.0      |
| per node, certifying RBs | 35   | 1539 | 0.105     | 95.0      |
| per node, certifying RBs | 44   | 1539 | 0.105     | 95.0      |
| per node, certifying RBs | 7    | 1539 | 0.107     | 96.0      |
| per node, certifying RBs | 31   | 1539 | 0.106     | 96.0      |
| per node, certifying RBs | 40   | 1539 | 0.107     | 96.0      |
| per node, certifying RBs | 28   | 1539 | 0.107     | 97.0      |
| per node, certifying RBs | 32   | 1539 | 0.108     | 97.0      |
| per node, certifying RBs | 38   | 1539 | 0.108     | 97.0      |
| per node, certifying RBs | 47   | 1539 | 0.108     | 97.0      |
| per node, certifying RBs | 50   | 1539 | 0.108     | 97.0      |
| per node, certifying RBs | 34   | 1539 | 0.108     | 98.0      |
| per node, certifying RBs | 8    | 1539 | 0.11      | 99.0      |
| per node, certifying RBs | 26   | 1539 | 0.111     | 100.0     |
