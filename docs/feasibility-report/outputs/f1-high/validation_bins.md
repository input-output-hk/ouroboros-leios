EBs of 1,000 to 1,500 transactions, the window's most common size class, 617 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current: IOG1, IOG3 | 0.09 to 0.09 (779) | 0.11 to 0.12 (177) | 0.13 to 0.18 (107) | 0.15 to 0.17 (50, tentative) | 0.17 to 0.18 (34, tentative) |
| r8id.xlarge, 4 vCPU, current: IOG2 | 0.10 (403) | 0.14 (59) | 0.14 (50) | 0.17 (36) | 0.18 (27, tentative) |
| c8id.xlarge, 4 vCPU, current: PIR1, PIR10, PIR3, PIR4, PIR8 | 0.10 to 0.11 (1614) | 0.12 to 0.14 (453) | 0.15 to 0.19 (368) | 0.17 to 0.25 (231, tentative) | 0.20 to 0.62 (210, tentative) |
| c5d.2xlarge, 8 vCPU, three older: PIR7, PIR9 | 0.16 to 0.16 (376) | 0.20 to 0.22 (207) | 0.29 to 0.30 (210) | 0.31 to 0.32 (134) | 0.37 to 0.88 (227) |
| c6id.2xlarge, 8 vCPU, two older: PIR2, PIR5, PIR6 | 0.13 to 0.17 (706) | 0.17 to 0.22 (306) | 0.25 to 0.28 (294) | 0.28 to 0.35 (187) | 0.31 to 0.44 (243) |
| operator nodes, the 51 with 20+ EBs of this size in every group, median node | 0.32 | 0.45 | 0.53 | 0.59 | 0.65 |
| lower quartile node | 0.19 | 0.25 | 0.30 | 0.32 | 0.37 |
| upper quartile node | 0.54 | 0.68 | 0.84 | 0.94 | 0.99 |
