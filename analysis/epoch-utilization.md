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
|        `550` | `7 725 300.464196` |  `67 431.504009` |
|        `549` | `7 728 511.864023` |  `56 324.445971` |
|        `548` | `7 765 678.546916` |  `53 136.772606` |
|        `547` | `7 840 690.098216` |  `54 873.551989` |
|        `546` | `7 870 624.686871` |  `53 377.937268` |
|        `545` | `7 726 349.523622` |  `63 417.467271` |
|        `544` | `7 753 134.590546` |  `66 943.752902` |
|        `543` | `7 795 722.908950` |  `99 113.874767` |
|        `542` | `7 901 127.670547` |  `73 755.360046` |
|        `541` | `7 871 007.443245` |  `74 074.183501` |
|        `540` | `7 981 229.354919` |  `76 503.073588` |
|        `539` | `7 975 418.752879` |  `67 915.279673` |
|        `538` | `7 822 513.376604` |  `76 469.312907` |
|        `537` | `7 980 990.385827` | `117 841.394966` |
|        `536` | `8 070 426.470838` |  `93 384.750236` |
|        `535` | `7 961 201.919637` | `102 941.304846` |
|        `534` | `8 106 461.541781` | `135 143.065318` |
|        `533` | `8 022 325.579285` |  `97 834.822698` |
|        `532` | `8 113 573.519941` |  `92 068.198245` |
|        `531` | `8 084 133.277015` | `107 386.764248` |
|        `530` | `7 995 335.103317` | `103 650.666676` |
|        `529` | `8 052 614.078075` | `113 830.599860` |
|        `528` | `8 108 593.264591` | `132 087.308893` |
|        `527` | `8 012 455.985771` | `158 411.032771` |
|        `526` | `8 072 808.756947` | `190 021.074276` |
|        `525` | `8 119 182.939729` | `211 458.647448` |

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
|----------------------------|
|      `12.8178815456265966` |

At this rate, the Reserve (and hence the rewards from it) will drop to half of its current amount in five years.

```sql
select 100 * exp(- 0.128178815456265966 * 5) as "Reserve in five years [%]";
```

| Reserve in five years [%] |
|--------------------------:|
|   `52.682119455527471200` |


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
    as "Full-block rate required to counteract shortfall [block/slot]"
  from generate_series(0, 10) as years;
```

| Year   | Full-block rate required to counteract shortfall [block/slot] |
|-------:|--------------------------------------------------------------:|
| `2025` |                          `0.00800000000000000000000000000000` |
| `2026` |                          `0.11224292690671381210236475926405` |
| `2027` |                          `0.20394501917987060985232319516215` |
| `2028` |                          `0.28461498861386355149670417569285` |
| `2029` |                          `0.35558004303265225855364775408655` |
| `2030` |                          `0.41800772193220000085312642037605` |
| `2031` |                          `0.47292510520913315954516648535505` |
| `2032` |                          `0.52123571100369565029699202692460` |
| `2033` |                          `0.56373436066564931068928531280460` |
| `2034` |                          `0.60112025540623565340803032778735` |
| `2035` |                          `0.63400847977740851193829374985305` |

Assuming current ada price and protocol parameters, this indicates that transaction throughput would have to increase to about one full Praos-like block every three seconds by 2029 to maintain rewards at current levels.
