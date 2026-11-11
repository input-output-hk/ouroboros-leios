| voter_ebs | voters | ebs  | voted  | too_late |
|----------:|-------:|-----:|-------:|---------:|
| 223346    | 88     | 3531 | 161530 | 59634    |
| EB size, txs | EBs | voters per EB | closure by 3 s / after 3 s / after 7 s or never | validation within 4 s / longer / never |
|---|---:|---:|---:|---:|
| under 2,000 | 907 | 70 | 73 / 13 / 13 % | 84 / 0 / 15 % |
| 2,000 to 4,000 | 900 | 70 | 68 / 22 / 10 % | 83 / 5 / 12 % |
| 4,000 to 6,000 | 1,190 | 68 | 62 / 21 / 17 % | 66 / 16 / 18 % |
| 6,000 and up | 531 | 66 | 52 / 26 / 22 % | 71 / 6 / 23 % |

| EB size, txs | EBs | voted in time / too late | late: closure arrived after 7 s / validation past 7 s / never validated | EBs with late voters over a quarter | certified, of the EBs the chain could certify |
|---|---:|---:|---:|---:|---:|
| under 2,000 | 907 | 83 / 16 % | 13 / 1 / 1 % | 19 % | 77 % |
| 2,000 to 4,000 | 900 | 79 / 19 % | 10 / 8 / 1 % | 26 % | 73 % |
| 4,000 to 6,000 | 1,190 | 62 / 37 % | 16 / 20 / 1 % | 72 % | 26 % |
| 6,000 and up | 531 | 65 / 34 % | 22 / 12 / 0 % | 76 % | 17 % |
