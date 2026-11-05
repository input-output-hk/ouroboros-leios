EBs of 1,500 to 2,000 transactions, the window's most common size class, 178 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current: IOG1, IOG3 | 0.16 to 0.19 (151) | 0.33 to 0.34 (64) | 0.47 to 0.47 (45, tentative) | 0.46 to 0.64 (40, tentative) | 0.46 to 0.63 (28, tentative) |
| r8id.xlarge, 4 vCPU, current: IOG2 | 0.16 (74) | 0.31 (26, tentative) | 0.40 (20, tentative) | 0.38 (20, tentative) | 0.41 (23, tentative) |
| c8id.xlarge, 4 vCPU, current: PIR1, PIR10, PIR3, PIR4, PIR8 | 0.16 to 0.21 (341) | 0.29 to 0.38 (162, tentative) | 0.52 to 0.57 (121, tentative) | 0.50 to 0.79 (110, tentative) | 0.65 to 0.83 (86, tentative) |
| c5d.2xlarge, 8 vCPU, three older: PIR7, PIR9 | 0.32 to 0.34 (136) | 0.58 to 0.61 (72) | 0.79 to 0.81 (50, tentative) | 1.02 to 1.08 (34, tentative) | 0.96 to 1.54 (36, tentative) |
| c6id.2xlarge, 8 vCPU, two older: PIR2, PIR5, PIR6 | 0.27 to 0.30 (217) | 0.46 to 0.52 (94, tentative) | 0.64 to 0.75 (64, tentative) | 0.70 to 0.92 (53, tentative) | 0.65 to 1.19 (60, tentative) |
| operator nodes, the 8 with 20+ EBs of this size in every group, median node | 0.37 | 0.57 | 0.79 | 0.88 | 1.00 |
| lower quartile node | 0.34 | 0.50 | 0.70 | 0.82 | 0.81 |
| upper quartile node | 0.82 | 1.29 | 1.68 | 1.96 | 2.06 |
