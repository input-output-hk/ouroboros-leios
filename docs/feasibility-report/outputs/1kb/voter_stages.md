| voter_ebs | voters | ebs | voted | too_late |
|----------:|-------:|----:|------:|---------:|
| 42797     | 85     | 608 | 35366 | 7405     |
| EB size, txs | EBs | voters per EB | closure by 3 s / after 3 s / after 7 s or never | validation within 4 s / longer / never |
|---|---:|---:|---:|---:|
| under 2,000 | 278 | 80 | 76 / 15 / 8 % | 88 / 2 / 10 % |
| 2,000 to 4,000 | 266 | 80 | 85 / 10 / 5 % | 87 / 7 / 6 % |
| 4,000 to 6,000 | 46 | 79 | 84 / 10 / 6 % | 70 / 22 / 9 % |
| 6,000 and up | 16 | 80 | 58 / 21 / 21 % | 32 / 45 / 23 % |

| EB size, txs | EBs | voted in time / too late | late: closure arrived after 7 s / validation past 7 s / never validated | EBs with late voters over a quarter | certified, of the EBs the chain could certify |
|---|---:|---:|---:|---:|---:|
| under 2,000 | 278 | 86 / 14 % | 8 / 4 / 1 % | 17 % | 67 % |
| 2,000 to 4,000 | 266 | 85 / 15 % | 5 / 9 / 1 % | 19 % | 45 % |
| 4,000 to 6,000 | 46 | 67 / 33 % | 6 / 24 / 3 % | 59 % | 4 % |
| 6,000 and up | 16 | 30 / 70 % | 21 / 47 / 2 % | 81 % | 11 % |
