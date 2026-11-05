| pooled over 188,299 records of 87 nodes | per applied transaction | per reapplied transaction | fixed per EB | residual | applied share, median record |
|---|---|---|---|---|---|
| fit | 1.36 ms | 0.114 ms | 0.39 s | 2.78 s | 2 % |

| per node, 85 nodes with 100 or more records | min | p25 | median | p75 | max |
|---|---|---|---|---|---|
| ms per applied transaction | 0.27 | 0.69 | 0.92 | 1.70 | 6.03 |
| ms per reapplied transaction | 0.053 | 0.152 | 0.201 | 0.444 | 2.240 |

| host class (instance, vCPU, generation) | hosts | EBs with 500+ applied, per host | ms per applied transaction | ms per reapplied transaction | fixed per EB |
|---|---|---|---|---|---|
| r8id.xlarge, 4 vCPU, current | IOG2 | 692 | 0.36 | 0.109 | 0.42 s |
| c6id.2xlarge, 8 vCPU, two older | PIR2, PIR5, PIR6 | 808 to 1332 | 0.34 to 0.50 | -0.042 to 0.133 | 0.79 to 1.55 s |
| c8id.xlarge, 4 vCPU, current | IOG1, IOG3 | 658 to 867 | 0.38 to 0.44 | -0.065 to 0.157 | 0.02 to 1.00 s |
| c8id.xlarge, 4 vCPU, current | PIR1, PIR10, PIR3, PIR4, PIR8 | 631 to 1318 | 0.30 to 0.48 | -0.091 to 0.138 | 0.30 to 1.26 s |
| c5d.2xlarge, 8 vCPU, three older | PIR7, PIR9 | 1264 to 1354 | 0.46 to 0.68 | -0.180 to 0.034 | 1.50 to 1.90 s |
