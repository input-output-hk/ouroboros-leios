|           what            |                kind                 | node_rbs | nodes | closure_B_p50 | txs_p50 | dur_p50_s | dur_p90_s | us_per_tx |
|---------------------------|-------------------------------------|---------:|------:|--------------:|--------:|----------:|----------:|----------:|
| pop to adopted by RB kind | c0 certifying, closure under 0.2 MB | 255      | 51    | 162200.0      | 811.0   | 0.074     | 0.095     | 91.0      |
| pop to adopted by RB kind | c1 certifying, closure 0.2-0.5 MB   | 5508     | 51    | 451000.0      | 2255.0  | 0.186     | 0.214     | 83.0      |
| pop to adopted by RB kind | c2 certifying, closure 0.5-0.9 MB   | 51765    | 51    | 555400.0      | 2777.0  | 0.222     | 0.251     | 80.0      |
| pop to adopted by RB kind | p0 plain, small                     | 1785     | 51    | NULL          | 0.0     | 0.002     | 0.002     | NULL      |
| pop to adopted by RB kind | p1 plain, full (80 kB+)             | 97685    | 51    | 555400.0      | 439.0   | 0.11      | 0.13      | 250.0     |
|                         what                         |               bin_a               |               bin_b               | us_per_tx | fixed_s |
|------------------------------------------------------|-----------------------------------|-----------------------------------|----------:|--------:|
| marginal us per closure tx (top two certifying bins) | c2 certifying, closure 0.5-0.9 MB | c1 certifying, closure 0.2-0.5 MB | 69.0      | 0.031   |
|                    what                     | certifying_p50_s | plain_full_p50_s | closure_txs | us_per_tx |
|---------------------------------------------|-----------------:|-----------------:|------------:|----------:|
| certifying minus plain full, per closure tx | 0.22             | 0.11             | 2777.0      | 40.0      |
|           what           | node | rbs  | dur_p50_s | us_per_tx |
|--------------------------|-----:|-----:|----------:|----------:|
| per node, certifying RBs | 37   | 1128 | 0.208     | 75.0      |
| per node, certifying RBs | 13   | 1128 | 0.21      | 76.0      |
| per node, certifying RBs | 14   | 1128 | 0.21      | 76.0      |
| per node, certifying RBs | 17   | 1128 | 0.21      | 76.0      |
| per node, certifying RBs | 29   | 1128 | 0.211     | 76.0      |
| per node, certifying RBs | 43   | 1128 | 0.21      | 76.0      |
| per node, certifying RBs | 46   | 1128 | 0.21      | 76.0      |
| per node, certifying RBs | 49   | 1128 | 0.211     | 76.0      |
| per node, certifying RBs | 4    | 1128 | 0.215     | 77.0      |
| per node, certifying RBs | 5    | 1128 | 0.215     | 77.0      |
| per node, certifying RBs | 16   | 1128 | 0.213     | 77.0      |
| per node, certifying RBs | 19   | 1128 | 0.214     | 77.0      |
| per node, certifying RBs | 23   | 1128 | 0.213     | 77.0      |
| per node, certifying RBs | 25   | 1128 | 0.214     | 77.0      |
| per node, certifying RBs | 31   | 1128 | 0.215     | 77.0      |
| per node, certifying RBs | 22   | 1128 | 0.216     | 78.0      |
| per node, certifying RBs | 41   | 1128 | 0.215     | 78.0      |
| per node, certifying RBs | 42   | 1128 | 0.217     | 78.0      |
| per node, certifying RBs | 45   | 1128 | 0.218     | 78.0      |
| per node, certifying RBs | 2    | 1128 | 0.22      | 79.0      |
| per node, certifying RBs | 9    | 1128 | 0.221     | 79.0      |
| per node, certifying RBs | 10   | 1128 | 0.219     | 79.0      |
| per node, certifying RBs | 12   | 1128 | 0.221     | 79.0      |
| per node, certifying RBs | 21   | 1128 | 0.219     | 79.0      |
| per node, certifying RBs | 24   | 1128 | 0.219     | 79.0      |
| per node, certifying RBs | 27   | 1128 | 0.218     | 79.0      |
| per node, certifying RBs | 44   | 1128 | 0.221     | 79.0      |
| per node, certifying RBs | 0    | 1128 | 0.222     | 80.0      |
| per node, certifying RBs | 6    | 1128 | 0.221     | 80.0      |
| per node, certifying RBs | 11   | 1128 | 0.222     | 80.0      |
| per node, certifying RBs | 15   | 1128 | 0.223     | 80.0      |
| per node, certifying RBs | 18   | 1128 | 0.223     | 80.0      |
| per node, certifying RBs | 33   | 1128 | 0.223     | 80.0      |
| per node, certifying RBs | 36   | 1128 | 0.223     | 80.0      |
| per node, certifying RBs | 39   | 1128 | 0.223     | 80.0      |
| per node, certifying RBs | 1    | 1128 | 0.226     | 81.0      |
| per node, certifying RBs | 3    | 1128 | 0.224     | 81.0      |
| per node, certifying RBs | 20   | 1128 | 0.225     | 81.0      |
| per node, certifying RBs | 30   | 1128 | 0.224     | 81.0      |
| per node, certifying RBs | 35   | 1128 | 0.225     | 81.0      |
| per node, certifying RBs | 7    | 1128 | 0.228     | 82.0      |
| per node, certifying RBs | 28   | 1128 | 0.227     | 82.0      |
| per node, certifying RBs | 32   | 1128 | 0.229     | 82.0      |
| per node, certifying RBs | 34   | 1128 | 0.229     | 82.0      |
| per node, certifying RBs | 38   | 1128 | 0.228     | 82.0      |
| per node, certifying RBs | 40   | 1128 | 0.229     | 82.0      |
| per node, certifying RBs | 47   | 1128 | 0.23      | 83.0      |
| per node, certifying RBs | 48   | 1128 | 0.231     | 83.0      |
| per node, certifying RBs | 8    | 1128 | 0.234     | 84.0      |
| per node, certifying RBs | 26   | 1128 | 0.233     | 84.0      |
| per node, certifying RBs | 50   | 1128 | 0.232     | 84.0      |
