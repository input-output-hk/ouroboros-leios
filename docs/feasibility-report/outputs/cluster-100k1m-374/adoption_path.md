|           what            |               kind                | node_rbs | nodes | closure_B_p50 | txs_p50 | dur_p50_s | dur_p90_s | us_per_tx |
|---------------------------|-----------------------------------|---------:|------:|--------------:|--------:|----------:|----------:|----------:|
| pop to adopted by RB kind | c1 certifying, closure 0.2-0.5 MB | 510      | 51    | 390082.0      | 1043.0  | 0.119     | 0.147     | 114.0     |
| pop to adopted by RB kind | c2 certifying, closure 0.5-0.9 MB | 9231     | 51    | 808588.0      | 2162.0  | 0.223     | 0.258     | 103.0     |
| pop to adopted by RB kind | c3 certifying, closure 0.9-1 MB   | 32079    | 51    | 999702.0      | 2673.0  | 0.272     | 0.304     | 102.0     |
| pop to adopted by RB kind | p0 plain, small                   | 1173     | 51    | 999702.0      | 0.0     | 0.002     | 0.003     | NULL      |
| pop to adopted by RB kind | p1 plain, full (80 kB+)           | 108320   | 51    | 999702.0      | 236.0   | 0.09      | 0.107     | 383.0     |
|                         what                         |              bin_a              |               bin_b               | us_per_tx | fixed_s |
|------------------------------------------------------|---------------------------------|-----------------------------------|----------:|--------:|
| marginal us per closure tx (top two certifying bins) | c3 certifying, closure 0.9-1 MB | c2 certifying, closure 0.5-0.9 MB | 96.0      | 0.015   |
|                    what                     | certifying_p50_s | plain_full_p50_s | closure_txs | us_per_tx |
|---------------------------------------------|-----------------:|-----------------:|------------:|----------:|
| certifying minus plain full, per closure tx | 0.265            | 0.09             | 2673.0      | 65.0      |
|           what           | node | rbs | dur_p50_s | us_per_tx |
|--------------------------|-----:|----:|----------:|----------:|
| per node, certifying RBs | 14   | 820 | 0.25      | 93.0      |
| per node, certifying RBs | 46   | 820 | 0.249     | 93.0      |
| per node, certifying RBs | 13   | 820 | 0.252     | 94.0      |
| per node, certifying RBs | 17   | 820 | 0.252     | 94.0      |
| per node, certifying RBs | 29   | 820 | 0.251     | 94.0      |
| per node, certifying RBs | 37   | 820 | 0.252     | 94.0      |
| per node, certifying RBs | 43   | 820 | 0.252     | 94.0      |
| per node, certifying RBs | 49   | 820 | 0.254     | 95.0      |
| per node, certifying RBs | 16   | 820 | 0.257     | 96.0      |
| per node, certifying RBs | 23   | 820 | 0.257     | 96.0      |
| per node, certifying RBs | 25   | 820 | 0.256     | 96.0      |
| per node, certifying RBs | 31   | 820 | 0.256     | 96.0      |
| per node, certifying RBs | 41   | 820 | 0.257     | 96.0      |
| per node, certifying RBs | 4    | 820 | 0.26      | 97.0      |
| per node, certifying RBs | 5    | 820 | 0.258     | 97.0      |
| per node, certifying RBs | 19   | 820 | 0.259     | 97.0      |
| per node, certifying RBs | 10   | 820 | 0.262     | 98.0      |
| per node, certifying RBs | 42   | 820 | 0.261     | 98.0      |
| per node, certifying RBs | 2    | 820 | 0.265     | 99.0      |
| per node, certifying RBs | 21   | 820 | 0.264     | 99.0      |
| per node, certifying RBs | 24   | 820 | 0.264     | 99.0      |
| per node, certifying RBs | 27   | 820 | 0.265     | 99.0      |
| per node, certifying RBs | 45   | 820 | 0.265     | 99.0      |
| per node, certifying RBs | 6    | 820 | 0.269     | 100.0     |
| per node, certifying RBs | 9    | 820 | 0.267     | 100.0     |
| per node, certifying RBs | 11   | 820 | 0.268     | 100.0     |
| per node, certifying RBs | 12   | 820 | 0.266     | 100.0     |
| per node, certifying RBs | 18   | 820 | 0.267     | 100.0     |
| per node, certifying RBs | 22   | 820 | 0.267     | 100.0     |
| per node, certifying RBs | 36   | 820 | 0.268     | 100.0     |
| per node, certifying RBs | 39   | 820 | 0.268     | 100.0     |
| per node, certifying RBs | 44   | 820 | 0.268     | 100.0     |
| per node, certifying RBs | 0    | 820 | 0.269     | 101.0     |
| per node, certifying RBs | 3    | 820 | 0.269     | 101.0     |
| per node, certifying RBs | 15   | 820 | 0.27      | 101.0     |
| per node, certifying RBs | 30   | 820 | 0.271     | 101.0     |
| per node, certifying RBs | 33   | 820 | 0.27      | 101.0     |
| per node, certifying RBs | 35   | 820 | 0.269     | 101.0     |
| per node, certifying RBs | 1    | 820 | 0.273     | 102.0     |
| per node, certifying RBs | 7    | 820 | 0.274     | 102.0     |
| per node, certifying RBs | 28   | 820 | 0.272     | 102.0     |
| per node, certifying RBs | 38   | 820 | 0.272     | 102.0     |
| per node, certifying RBs | 50   | 820 | 0.273     | 102.0     |
| per node, certifying RBs | 32   | 820 | 0.275     | 103.0     |
| per node, certifying RBs | 34   | 820 | 0.274     | 103.0     |
| per node, certifying RBs | 40   | 820 | 0.276     | 103.0     |
| per node, certifying RBs | 20   | 820 | 0.278     | 104.0     |
| per node, certifying RBs | 47   | 820 | 0.278     | 104.0     |
| per node, certifying RBs | 8    | 820 | 0.281     | 105.0     |
| per node, certifying RBs | 26   | 820 | 0.28      | 105.0     |
| per node, certifying RBs | 48   | 820 | 0.283     | 106.0     |
