EBs of 4,000 to 5,999 transactions: chained closures, certified closures in which 80 % or more of the inputs spend an output of the same block, 1 EBs; old-input closures, certified closures in which 50 % or less of the inputs spend an output of the same block, 0 EBs; the db-sync composition holds 20 certified closures of the class, chained closures 1 (median transaction size 247 B) and old-input closures 19 (median transaction size 220 B); a host cell resting on fewer than 10 EBs is marked tentative.

| host class (instance, vCPU, generation) | hosts | chained closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | old-input closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | EBs validated per host |
|---|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current (IOG) | IOG1, IOG3 | - (0) tentative | 72 to 79 (1) tentative | - | - | 1; - |
| r8id.xlarge, 4 vCPU, current (IOG) | IOG2 | - (0) tentative | 72 (1) tentative | - | - | 1; - |
| c8id.xlarge, 4 vCPU, current (PIR) | PIR1, PIR10, PIR3, PIR4, PIR8 | - (0) tentative | 76 to 86 (0 to 1) tentative | - | - | 1; - |
| c6id.2xlarge, 8 vCPU, two older (PIR) | PIR2, PIR5, PIR6 | - (0) tentative | 120 to 125 (0 to 1) tentative | - | - | 1; - |
| c5d.2xlarge, 8 vCPU, three older (PIR) | PIR7, PIR9 | - (0) tentative | 132 (0 to 1) tentative | - | - | 1; - |

