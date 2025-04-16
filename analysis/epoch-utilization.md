# Motivating Leios: Fees and rewards

Given the current protocol parameters on `mainnet` and historical ada prices, even fully utilized Praos blocks do not generate sufficient fees to cover stakepool operating costs. However, higher transaction throughput on `mainnet` can generate sufficient fees to cover the cost of operating stakepool under Praos or Leios.


## Maximum theoretical fee for a block or epoch

The protocol parameters for Epoch 550 are shown in the following table.

| Parameter            | Value         | Units         |
|----------------------|--------------:|---------------|
| `max_block_size`     |       `90112` | byte/block    |
| `min_fee_a`          |          `44` | lovelace/byte |
| `min_fee_b`          |      `155381` | lovelace/tx   |
| `max_block_ex_mem`   |    `62000000` | me/block      |
| `price_mem`          |      `0.0577` | lovelace/mem  |
| `max_block_ex_steps` | `20000000000` | ste/block     |
| `price_step`         |    `7.21e-05` | lovelace/step |

From historical data, we see that approximately 75 tx/block is the maximum number of transactions practically included in a full block. Each epoch has an average of 21,600 blocks.

Now estimate the approximate maximum fee possible for a block or epoch:

| Item             | Computation                       | Fee [lovelace/block] | Fee [ADA/epoch]  |
|------------------|-----------------------------------|---------------------:|-----------------:|
| Bytes            | `max_block_size * min_fee_a`      |         `3 964 928`  |        `85 642`  |
| Transactions     | `75 * min_fee_b`                  |        `11 653 575`  |       `251 717`  |
| Execution memory | `max_block_ex_mem * price_mem`    |         `3 577 400`  |        `77 272`  |
| Execution steps  | `max_block_ex_steps * price_step` |         `1 442 000`  |        `31 147`  |
| *Total*          |                                   |       *`20 637 903`* |      *`445 778`* |


## Current rewards and fees

Recent epochs distribute about eight million ada in rewards.

```sql
select
    earned_epoch as "Epoch Earned"
  , sum(amount) / 1e6 as "Reward [ADA/epoch]"
  , fees / 1e6 as "Fees [ADA/Epoch]"
  from reward
  inner join ada_pots
    on earned_epoch = epoch_no - 1
  where earned_epoch between 525 and 550
  group by earned_epoch, epoch_no, fees
order by earned_epoch desc;
```

| Epoch Earned | Reward [ADA/epoch] | Fees [ADA/Epoch] |
|-------------:|-------------------:|-----------------:|
|        `550` |        `7 725 300` |         `67 431` |
|        `549` |        `7 728 511` |         `56 324` |
|        `548` |        `7 765 678` |         `53 136` |
|        `547` |        `7 840 690` |         `54 873` |
|        `546` |        `7 870 624` |         `53 377` |
|        `545` |        `7 726 349` |         `63 417` |
|        `544` |        `7 753 134` |         `66 943` |
|        `543` |        `7 795 722` |         `99 113` |
|        `542` |        `7 901 127` |         `73 755` |
|        `541` |        `7 871 007` |         `74 074` |
|        `540` |        `7 981 229` |         `76 503` |
|        `539` |        `7 975 418` |         `67 915` |
|        `538` |        `7 822 513` |         `76 469` |
|        `537` |        `7 980 990` |        `117 841` |
|        `536` |        `8 070 426` |         `93 384` |
|        `535` |        `7 961 201` |        `102 941` |
|        `534` |        `8 106 461` |        `135 143` |
|        `533` |        `8 022 325` |         `97 834` |
|        `532` |        `8 113 573` |         `92 068` |
|        `531` |        `8 084 133` |        `107 386` |
|        `530` |        `7 995 335` |        `103 650` |
|        `529` |        `8 052 614` |        `113 830` |
|        `528` |        `8 108 593` |        `132 087` |
|        `527` |        `8 012 455` |        `158 411` |
|        `526` |        `8 072 808` |        `190 021` |
|        `525` |        `8 119 182` |        `211 458` |

Thus, even the fees from full blocks would only amount to six percent of current rewards. Current fees are approximately fifteen percent of the theoretical maximum.


## Depletion of the Reserve

Most of the rewards currently come from the Reserve, but that Reserve is depleting at the rate of about thirteen percent per year.

```sql
select
    100 * ln( 1.0
      * (select reserves from ada_pots where epoch_no = 350)
      / (select reserves from ada_pots where epoch_no = 550)
    ) / ((550 - 350) / (365.24 / 5)) as "Reserve depletion [%/year]" ;
```

| Reserve depletion [%/year] |
|---------------------------:|
|                    `12.81` |

At this rate, the Reserve (and hence the rewards from it) will drop to half of its current amount in five years.

```sql
select 100 * exp(- 0.128178815456265966 * 5) as "Reserve in five years [%]";
```

| Reserve in five years [%] |
|--------------------------:|
|                   `52.68` |


## Implications for Leios

Anecdotal evidence indicates that the current rewards and ada price are approximately sufficient for stakepools to be profitable. How much would the production rate of full Praos blocks have to be in order to make up the shortfall of decreasing Reserve?

```sql
select
    2025 + years "Year"
  , (select sum(amount) / 1e6 from reward where earned_epoch = 550) -- Current rewards
    * (1 - exp(- 0.128178815456265966 * years))                     -- Shortfall from diminishing Reserve
    / 445778                                                        -- Maximum Praos fee per epoch
    * 0.05                                                          -- Praos active slot coefficient
    + 0.16 * 0.05                                                   -- Current Praos utilization
    as "Full-block rate required to maintain rewards [block/slot]"
  from generate_series(0, 10) as years;
```

| Year   | Full-block rate required to maintain rewards [block/slot] |
|-------:|----------------------------------------------------------:|
| `2025` |                                                   `0.008` |
| `2026` |                                                   `0.112` |
| `2027` |                                                   `0.203` |
| `2028` |                                                   `0.284` |
| `2029` |                                                   `0.355` |
| `2030` |                                                   `0.418` |
| `2031` |                                                   `0.472` |
| `2032` |                                                   `0.521` |
| `2033` |                                                   `0.563` |
| `2034` |                                                   `0.601` |
| `2035` |                                                   `0.634` |

Assuming current ada price and protocol parameters, this indicates that transaction throughput would have to increase to about one full Praos-like block every three seconds by 2029 to maintain rewards at current levels.
