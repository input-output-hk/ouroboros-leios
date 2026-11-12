|           what            |               kind                | node_rbs | nodes | closure_B_p50 | txs_p50 | dur_p50_s | dur_p90_s | us_per_tx |
|---------------------------|-----------------------------------|---------:|------:|--------------:|--------:|----------:|----------:|----------:|
| pop to adopted by RB kind | c1 certifying, closure 0.2-0.5 MB | 51       | 51    | 384846.0      | 1029.0  | 0.125     | 0.137     | 121.0     |
| pop to adopted by RB kind | c2 certifying, closure 0.5-0.9 MB | 1020     | 51    | 808588.0      | 2162.0  | 0.219     | 0.244     | 101.0     |
| pop to adopted by RB kind | c3 certifying, closure 0.9-1 MB   | 72053    | 51    | 999702.0      | 2673.0  | 0.268     | 0.303     | 100.0     |
| pop to adopted by RB kind | p0 plain, small                   | 1377     | 51    | NULL          | 0.0     | 0.002     | 0.002     | NULL      |
| pop to adopted by RB kind | p1 plain, full (80 kB+)           | 76112    | 51    | 999702.0      | 236.0   | 0.09      | 0.107     | 380.0     |
|                         what                         |              bin_a              |               bin_b               | us_per_tx | fixed_s |
|------------------------------------------------------|---------------------------------|-----------------------------------|----------:|--------:|
| marginal us per closure tx (top two certifying bins) | c3 certifying, closure 0.9-1 MB | c2 certifying, closure 0.5-0.9 MB | 96.0      | 0.012   |
|                    what                     | certifying_p50_s | plain_full_p50_s | closure_txs | us_per_tx |
|---------------------------------------------|-----------------:|-----------------:|------------:|----------:|
| certifying minus plain full, per closure tx | 0.268            | 0.09             | 2673.0      | 67.0      |
|           what           | node | rbs  | dur_p50_s | us_per_tx |
|--------------------------|-----:|-----:|----------:|----------:|
| per node, certifying RBs | 46   | 1434 | 0.25      | 94.0      |
| per node, certifying RBs | 29   | 1434 | 0.254     | 95.0      |
| per node, certifying RBs | 37   | 1434 | 0.254     | 95.0      |
| per node, certifying RBs | 49   | 1434 | 0.255     | 95.0      |
| per node, certifying RBs | 14   | 1434 | 0.259     | 97.0      |
| per node, certifying RBs | 17   | 1434 | 0.26      | 97.0      |
| per node, certifying RBs | 0    | 1434 | 0.262     | 98.0      |
| per node, certifying RBs | 3    | 1434 | 0.263     | 98.0      |
| per node, certifying RBs | 13   | 1434 | 0.262     | 98.0      |
| per node, certifying RBs | 16   | 1434 | 0.261     | 98.0      |
| per node, certifying RBs | 19   | 1434 | 0.263     | 98.0      |
| per node, certifying RBs | 23   | 1434 | 0.261     | 98.0      |
| per node, certifying RBs | 25   | 1434 | 0.261     | 98.0      |
| per node, certifying RBs | 41   | 1434 | 0.262     | 98.0      |
| per node, certifying RBs | 42   | 1434 | 0.263     | 98.0      |
| per node, certifying RBs | 45   | 1434 | 0.262     | 98.0      |
| per node, certifying RBs | 4    | 1434 | 0.264     | 99.0      |
| per node, certifying RBs | 10   | 1434 | 0.266     | 99.0      |
| per node, certifying RBs | 20   | 1434 | 0.264     | 99.0      |
| per node, certifying RBs | 24   | 1434 | 0.265     | 99.0      |
| per node, certifying RBs | 43   | 1434 | 0.265     | 99.0      |
| per node, certifying RBs | 48   | 1434 | 0.266     | 99.0      |
| per node, certifying RBs | 2    | 1434 | 0.267     | 100.0     |
| per node, certifying RBs | 6    | 1434 | 0.267     | 100.0     |
| per node, certifying RBs | 9    | 1434 | 0.268     | 100.0     |
| per node, certifying RBs | 27   | 1434 | 0.268     | 100.0     |
| per node, certifying RBs | 31   | 1434 | 0.266     | 100.0     |
| per node, certifying RBs | 39   | 1434 | 0.268     | 100.0     |
| per node, certifying RBs | 5    | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 12   | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 15   | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 21   | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 30   | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 33   | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 36   | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 44   | 1434 | 0.27      | 101.0     |
| per node, certifying RBs | 11   | 1434 | 0.273     | 102.0     |
| per node, certifying RBs | 18   | 1434 | 0.273     | 102.0     |
| per node, certifying RBs | 22   | 1434 | 0.273     | 102.0     |
| per node, certifying RBs | 28   | 1434 | 0.273     | 102.0     |
| per node, certifying RBs | 35   | 1434 | 0.272     | 102.0     |
| per node, certifying RBs | 1    | 1434 | 0.274     | 103.0     |
| per node, certifying RBs | 7    | 1434 | 0.276     | 103.0     |
| per node, certifying RBs | 38   | 1434 | 0.275     | 103.0     |
| per node, certifying RBs | 34   | 1434 | 0.278     | 104.0     |
| per node, certifying RBs | 32   | 1434 | 0.28      | 105.0     |
| per node, certifying RBs | 40   | 1434 | 0.281     | 105.0     |
| per node, certifying RBs | 47   | 1434 | 0.281     | 105.0     |
| per node, certifying RBs | 50   | 1434 | 0.284     | 106.0     |
| per node, certifying RBs | 26   | 1434 | 0.285     | 107.0     |
| per node, certifying RBs | 8    | 1424 | 0.29      | 109.0     |
