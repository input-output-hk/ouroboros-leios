EBs of 4,500 to 5,000 transactions, the window's most common size class, 367 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current: IOG1, IOG3 | 0.40 to 0.43 (417) | 1.22 to 1.32 (132) | 2.13 to 2.25 (93) | 2.90 to 3.18 (52, tentative) | 3.69 to 3.92 (22, tentative) |
| r8id.xlarge, 4 vCPU, current: IOG2 | 0.37 (275) | 1.35 (46) | 2.40 (25, tentative) | - | - |
| c8id.xlarge, 4 vCPU, current: PIR1, PIR10, PIR3, PIR4, PIR8 | 0.43 to 0.54 (924) | 1.31 to 1.64 (327) | 2.36 to 2.74 (244) | 3.58 to 3.71 (157, tentative) | 4.60 to 4.98 (111, tentative) |
| c5d.2xlarge, 8 vCPU, three older: PIR7, PIR9 | 0.86 to 0.92 (302) | 2.05 to 2.54 (142) | 4.05 to 4.09 (114) | 5.57 to 5.68 (73, tentative) | 7.11 to 7.95 (90) |
| c6id.2xlarge, 8 vCPU, two older: PIR2, PIR5, PIR6 | 0.66 to 0.81 (545) | 1.87 to 2.08 (196) | 3.16 to 3.44 (158) | 4.52 to 4.72 (111, tentative) | 5.43 to 5.97 (58, tentative) |
| operator nodes, the 13 with 20+ EBs of this size in every group, median node | 1.45 | 3.19 | 6.17 | 8.94 | 10.53 |
| lower quartile node | 0.95 | 2.06 | 3.69 | 5.14 | 6.57 |
| upper quartile node | 2.01 | 5.57 | 10.89 | 14.86 | 19.01 |
