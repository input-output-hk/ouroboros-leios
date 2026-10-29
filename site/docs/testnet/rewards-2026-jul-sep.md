---
sidebar_position: 4
sidebar_label: "Rewards: July to September 2026"
slug: /testnet/rewards-2026-jul-sep
hide_table_of_contents: true
description: MusashiNet Rewards Program results for July, August and September 2026, one row per registered stake pool, with the notice and review procedure.
keywords:
  - leios
  - musashinet
  - testnet
  - stake pool
  - incentives
  - rewards
---

# MusashiNet rewards: July to September 2026

One row per registered stake pool. A pool earns **$100 for each month** it qualifies, for up to three pools per participant. Where a participant registered more than once, pools from all their registrations count towards the three; if there are more than three, the pools in their latest registration take priority.

- **KYC:** the participant's identity verification and wallet check are both complete. Rewards are paid only to participants who completed KYC. ❌ means the checks were not completed within the KYC period, which has now closed.
- **Jul blocks:** the pool produced at least one block on MusashiNet in July.
- **Aug blocks (10-31):** the pool produced at least one block on MusashiNet from 10 August, when the network was reset. Blocks from 1 to 9 August alone do not cover most of the month and do not qualify.
- **Sep blocks** and **Sep data:** the pool produced at least one block in September **and** shared data through Metsuke. Data shared up to 2026-10-15 counts for September. Data from another network does not count.
- **USD:** the pool's total rewards for July to September, in US dollars.
- **Shared relays:** a participant's pools must not share relay nodes, because pools behind a single relay look like a single pool to the rest of the network. Where pools of the same participant declared the same relay for more than 48 hours in a month, only one of them is paid for that month: the one that produced the most blocks. This applies from August, when the rewards programme started; July is rewarded retroactively and every pool that produced blocks is paid.

Block counts come from KleioScan (kleioscan.com) for the MusashiNet networks that ran during each month. Data sharing comes from the Metsuke collection records.

<div className="rewards-table">

| # | Pool ID | KYC | Jul blocks | Aug blocks (10-31) | Sep blocks | Sep data | USD | Notes |
|---:|---|---|---|---|---|---|---:|---|
| 1 | `pool102xtd26h9r7dw068zdc5645r736793lujx7fpgcfmajhyxs7ny8` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 |  |
| 2 | `pool10cp6lxlu8g5aaur0slsqkks7rlv4dh2fzylwyvk7amftkhq0dxd` | ❌ | ✅ | ❌ | ❌ | ❌ | 0 | KYC not completed |
| 3 | `pool10f0c7vmlrfnf75vqklca35eux9h5w5a8xl53elkcd5ma7dsd9zh` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 4 | `pool10teel6z48x9nk9cjgrks08hc377xqfru3csr3qk338nzv8jmpts` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 5 | `pool120jqkadvew8c7mm6hrxesqd0nftwl723v9xh9k69g35zc9ee5qu` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Over the 3-pool limit for its participant (the latest registration's pools take priority), not paid |
| 6 | `pool12egzayyh8v75amsks3f9j2c0sk7nh7c6j9tvy4e48al0qxzcvzf` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay https://testicles.kiwipool.org:9740 with pool1lknnhwa… for 26 h, under the 48-hour limit; no deduction; Sep: shared relay https://testicles.kiwipool.org:9740 with pool1lknnhwa… for 1.9 h, under the 48-hour limit; no deduction |
| 7 | `pool12l2s7zxccvqn5qvurtfxqvsydz0hmsff7q74zfzuamsaza9y9ln` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay 167.86.96.40:3010 with pool1mp5lp56… for 0.6 h, under the 48-hour limit; no deduction |
| 8 | `pool12m2d2xffx3ffmakpjk5a5rq0m8rlgwf9tuu2v26lx90tqygjvxl` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 9 | `pool13hxxx94chph7zydyjfyp6y9wd753nxayner52eng5adyy7zedlp` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay 138.229.21.34:3010 142.127.64.153:3010 142.170.109.183:3010 with pool1l42lxnc… for 38 h, under the 48-hour limit; no deduction; Sep: shared relay 138.229.21.34:3010 142.127.64.153:3010 with pool1l42lxnc… for 6.7 h, under the 48-hour limit; no deduction; Relay 138.229.21.34:3010, now shared with pool1l42lxnc…, was added by this pool's re-registration on 2026-10-14, after the period |
| 10 | `pool13keum7zvprmyjgyfkgsh85s6l39wt7xq8q6xhl7d0slqkz66jf0` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no blocks |
| 11 | `pool14497fyzuzztzkj33gac39rlq84fsn3xuehtaqkg6y5t7wrrhrsm` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 |  |
| 12 | `pool144tj43y9xq0mkxafd8af42xf07u2nj4p8j79s9uahe29v2mt3hv` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no blocks |
| 13 | `pool1450xdy6e7lgrsmpwytg2c705m7h3gnucphpc566egwqez5h53mx` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Aug: shared relay 169.58.225.146:3010 with pool156c7dvm… for 1.7 h, under the 48-hour limit; no deduction; Sep: no Metsuke data; Sep: shared relay 169.58.239.205:3010 with pool1hfk89yg… for 75 h; relay 169.58.239.205:3010 with pool156c7dvm… for 75 h, over the 48-hour limit; allowed as a temporary move, each pool on its own relay for the rest of the month |
| 14 | `pool14fshd5xe9h59d442p7y8ck3hs5xpdt2qts9up43zjaxhwpg36dx` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 15 | `pool14xj9y60k9478tk76uhhyrxz4j2pz2acaqf28d3cl9lc3cegp05v` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 16 | `pool156c7dvmq07c4afy98j2skwt94qkhqd7te8vl4tc03z3djuz46wq` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Aug: shared relay 169.58.225.146:3010 with pool1450xdy6… for 1.7 h, under the 48-hour limit; no deduction; Sep: no Metsuke data; Sep: shared relay 169.58.239.205:3010 with pool1hfk89yg… for 75 h; relay 169.58.239.205:3010 with pool1450xdy6… for 75 h, over the 48-hour limit; allowed as a temporary move, each pool on its own relay for the rest of the month |
| 17 | `pool15at6zpa4jrswwx6r7rzztnwjtf8653ppdkzamqr3d3xp260ay3n` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Sep data shared in October, counted for September |
| 18 | `pool15chcuzu7rsdvm7z9qpplflh0k94vt465jw6wve3947x26e7zx7g` | ✅ | ❌ | ❌ | ✅ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no Metsuke data |
| 19 | `pool15dxt6c98u3l0zqr95r8yk64573n0fgxc83tlh37l0vclyuz9n6y` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 20 | `pool15mlfwa82pzqhmayx4ydne3nnfyrnsmcgyrfl3z69acxuklqtquy` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 21 | `pool15svjdp7tnrju6qrdrgslmutrtcl5ys25avnqv4csukh2zgvgvex` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Aug: shared relay 109.228.52.195:3010 with pool1gfgvkyd… for 0.1 h; relay 109.228.52.195:3010 with pool1qvh8lse… for 0.1 h, under the 48-hour limit; no deduction |
| 22 | `pool15y5lrrm3fyvrtllpn85kxate0x3q6e7d6rdzqpsp88275m6jhup` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Replaced in its registration by pool17hcgfm4…, the pool the operator ran with the same application code; not paid |
| 23 | `pool16ag9njq9yqus5y0pz0nmzmxa0ep6kuaufatltmrljlaev548pyu` | ❌ | ❌ | ❌ | ✅ | ❌ | 0 | KYC not completed; Sep: shared relay 178.168.53.97:3010 with pool1gjymgja… for 45 h, under the 48-hour limit; no deduction |
| 24 | `pool17at5slyy52ssulc02pvqpues9gp7s2ey7cf6mphl97nl79k4255` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 25 | `pool189awmnyzhmcjysa2kacgzpkgkdznqrkgtjuvpfxaxejlqhypfug` | ✅ | ❌ | ❌ | ✅ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no Metsuke data; Sep: shared relay 169.58.237.170:3010 with pool1zqfgsce… for 88 h, over the 48-hour limit; no deduction, as at most one of the pools qualified that month |
| 26 | `pool18jf7tcx0432rmmzdhr2em7wcnssse2737cnhhxy49jjcqqr8a7r` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 27 | `pool19hfcy8n4ygj7g5e9ljj5tkref6gqq5a7w9jp9wag26wv5tv0vrl` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 28 | `pool19vlckzxxpz32dj5j84xtzut40tz002w6me6a6vc328v5yqrd2jx` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 29 | `pool1a03qmcv5gassny47nnygnx4pzn3gvwf62ttqdtjk2tfwc2ts3xk` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 30 | `pool1a56y6jg0ycq74nk2hr0ranusrefenl0s422mnnmqpqf32hmzw2e` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 31 | `pool1aed7mtekax9pslhpnsydqwmg02uph38c35addynpdrufjaynkpu` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 32 | `pool1agplfadvkvvpzd2gymlknn32x7ju4lqg3ynemdtjv48c6qvvp4p` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 33 | `pool1ash2ka36g6hmvr90njmfvquuwsc5f6hs632970gkkwyp2rpumke` | ✅ | ❌ | ❌ | ✅ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no Metsuke data |
| 34 | `pool1ay0cvg7xpypchd2qmw7xm3796tv6qrzx57xy8wqv3djw72gqg7l` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; allow-list* |
| 35 | `pool1cp8dkjh5zf5tga3gr8qsr8j6n29unrwy4wf9dm9shh35xtps0e6` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay musashi.happystaking.io:3005 with pool1r6csfcp… for 44 h, under the 48-hour limit; no deduction |
| 36 | `pool1cptlr8wyr92hm3shazrm6huyph4p2h4wg8uffl5aga07srzsvg8` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 37 | `pool1cpw3tfwaxq3ejkdsg748kn68t3rkk5anmfegtqqlxj8fgax44k3` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 38 | `pool1dkf08rprdqwt0qmlgzvpwmplm74ry5w22p9fg03eeqyjs7ylu84` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 39 | `pool1dmt6hr0d7nrxcqhkgdckar33vty3j68zlt936tu3cp0wc3jyevl` | ✅ | ✅ | ✅ | ✅ | ❌ | 200 | Sep: no Metsuke data |
| 40 | `pool1eay9exv7p7jhw6c4nggdglwvpgggsccax8t50n03wmjysm8xagh` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Replaced in its registration by pool185ztd8n…, the pool the operator ran with the same application code; not paid |
| 41 | `pool1ecp2e7yv75sw3y32kfx7hy8vc5fewflrm9wa7jps2r8ukn92y3z` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 42 | `pool1ectn8ffx5w0x8xf4maczug5p4f5qscpe8wzm8kzwz4ydxdctkvg` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no blocks |
| 43 | `pool1eglx5vk8wfm959q8rngvq4et8j80qftjrakl37ehhammkqu8u0v` | ❌ | ❌ | ❌ | ✅ | ✅ | 0 | KYC not completed |
| 44 | `pool1ektalsfq2dtz939ng9ms4yzj0sudytxs376q4jmxmcea67jd35a` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 |  |
| 45 | `pool1evtdu3h7qpqajatunktdcrmp6ef2dgwnurkdk62qm8hzzptp3dl` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 46 | `pool1f6wrh4zus9cadzefllya2v40pj9ldfply3svlkk53282u3nyuke` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 47 | `pool1f9uzdhw85t677pd7epqsnph5uuhcv52r5y4ukpmtjswguryq05a` | ❌ | ❌ | ❌ | ❌ | ❌ | 0 | KYC not completed |
| 48 | `pool1fdn7sfg604fvqgjl0k2ppmntkcrak8vcmrgag39k6fmhzmvz262` | ✅ | ❌ | ✅ | ❌ | ❌ | 0 | Replaced in its registration by pool1as25z5l…, the pool the operator ran with the same application code; not paid |
| 49 | `pool1flmxn959lazu4nsrxyaxj6wa3yz7pjd3y7dam5xmg3zqytc779f` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 50 | `pool1fqgsajsa8ekrcg2d46wtuwhufrefae2mqnyzmdhnshe9xq7wce9` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 51 | `pool1fxe345ex6mdsxgfsts2w6f8rxhfazdtn8geuz93fqwsgjj3dz2s` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 52 | `pool1g9h4y4x4u7jhyn6cv6fegt8gp79trkk34f0g7lqat8ms5r5c8au` | ✅ | ❌ | ✅ | ✅ | ✅ | 0 | Jul: no blocks; Aug: shared relay 62.84.177.82:3010 with pool1zfeup8l… for 161 h; relay 62.84.177.82:3010 with pool1vrnkhhh… for 161 h, over the 48-hour limit; not paid, pool1zfeup8l… paid instead as the pool with most blocks; Sep data shared in October, counted for September; Sep: shared relay 62.84.177.82:3010 with pool1zfeup8l… for 709 h; relay 62.84.177.82:3010 with pool1vrnkhhh… for 228 h, over the 48-hour limit; not paid, pool1zfeup8l… paid instead as the pool with most blocks |
| 53 | `pool1gcerdtrqfurel2qjvdt98fpxazxxvvx77xnz9g22husc2frzfa2` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Sep data shared in October, counted for September |
| 54 | `pool1gfeygmd86hgcg2dft2g3vx7u824rl29m2llzy9rl0mhcc2nh8s4` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Sep data shared in October, counted for September |
| 55 | `pool1gfgvkydaj24yypsyjcawg4dnjyrpcs9h7j8ldzuty7j5xaf5luf` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay 109.228.52.195:3010 with pool1qvh8lse… for 1.5 h; relay 109.228.52.195:3010 with pool15svjdp7… for 0.1 h, under the 48-hour limit; no deduction |
| 56 | `pool1gjymgja7vq9k6ajy3d5ygqxymctpdsqvja5yw8qf4kx3kpjc6su` | ❌ | ❌ | ✅ | ✅ | ❌ | 0 | KYC not completed; Sep: shared relay 178.168.53.97:3010 with pool16ag9njq… for 45 h, under the 48-hour limit; no deduction |
| 57 | `pool1gt5lq6dl9mlfy770xwu4lvzn3l03nxxhkhj07rd4wpr8yv6aw0j` | ❌ | ❌ | ❌ | ✅ | ✅ | 0 | KYC not completed |
| 58 | `pool1gv4dg0u9egfts87d8jukzu68sa85hhtvvlpunmq7vry4zpfu4my` | ✅ | ❌ | ❌ | ✅ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no Metsuke data |
| 59 | `pool1gvagur2fvv2yf8cd0zleljfmgygmq727ct0d5te7dfaaz6xapg7` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Over the 3-pool limit for its participant (the latest registration's pools take priority), not paid |
| 60 | `pool1h9mquxald2tcu0lsccfzf6ntr8r7mu8qu3htj5z6fay26mqkxep` | ❌ | ❌ | ❌ | ✅ | ✅ | 0 | KYC not completed |
| 61 | `pool1hfk89ygm2xmn36grhyp7wmycdpc5u4kg5wldpscmfeajshemh4k` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data; Sep: shared relay 169.58.239.205:3010 with pool156c7dvm… for 75 h; relay 169.58.239.205:3010 with pool1450xdy6… for 75 h, over the 48-hour limit; allowed as a temporary move, each pool on its own relay for the rest of the month |
| 62 | `pool1hts9z229runn8lrh2h5kcr9am9hypfr48080nxeerarpklym2sd` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 63 | `pool1jmatwe3tygtufld2n5xaf7ac4568elg64zprvrup76wqqkcj3m9` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Sep data shared in October, counted for September |
| 64 | `pool1jqrxz3x602t5xj6k35m585zvzfr5cd6kcwx2metsjnnj6j4y75s` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 65 | `pool1jruvurjh23a452kck8gqkqnj7uuy8a2arnavzmg8vlj3gla23qz` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no blocks |
| 66 | `pool1jty4qara5gffpju9etgasgd2yfpxwrc6cpfhtz63507n55sz56c` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 67 | `pool1jvpqkhmh8cefx4v208aj2h4g3grv4a4dwmg8hvglu9ed5twrhcz` | ❌ | ❌ | ❌ | ❌ | ❌ | 0 | KYC not completed |
| 68 | `pool1ktpevs7xl4qgaqs4mczfsp7j7qx7aytyhegvqmml40z8c05gg6p` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks; Sep data shared in October, counted for September |
| 69 | `pool1l42lxnce9e78ec3stxla7wewsl7t9erh45kll9zgtqtucgtjy9k` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay 138.229.21.34:3010 142.127.64.153:3010 142.170.109.183:3010 with pool13hxxx94… for 38 h, under the 48-hour limit; no deduction; Sep: shared relay 138.229.21.34:3010 142.127.64.153:3010 with pool13hxxx94… for 6.7 h, under the 48-hour limit; no deduction; Relay 138.229.21.34:3010 is now also declared by pool13hxxx94c…, from that pool's re-registration on 2026-10-14, after the period |
| 70 | `pool1lknnhwa9xnawxmlmmnxxnep2485d0wvzsa794yrcv9r3w9z7mq8` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay https://testicles.kiwipool.org:9740 with pool12egzayy… for 26 h, under the 48-hour limit; no deduction; Sep: shared relay https://testicles.kiwipool.org:9740 with pool12egzayy… for 1.9 h, under the 48-hour limit; no deduction |
| 71 | `pool1lq8wzf9qszts4c8jnqk8a3tv4sney8m2yeze03x8c5l759dcv9` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Over the 3-pool limit for its participant (the latest registration's pools take priority), not paid |
| 72 | `pool1lq96uvgznlqr0j7m8ftpzdqq03vg8ny78dcmdffj4zn8j35e67j` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 73 | `pool1mp5lp56jk9jp6f3fh0psn440x6pqtkd53rtnvws0lc80w4j8ztm` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 | Aug: shared relay 167.86.96.40:3010 with pool12l2s7zx… for 0.6 h, under the 48-hour limit; no deduction |
| 74 | `pool1mzj6lyaws8fcxh9crqpnxaqca0m92ht6r0ceg9egnhntj005pz5` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 75 | `pool1n473t9z42nldn5286fwqvxz7zfpnzl9qs0yuzf7wzr9nkpregc5` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 76 | `pool1n7h0an706ye0nuy5up88k6ljqx79jxf3zr6qle7pkaw7xwxlkkt` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 77 | `pool1nk9mvga8k6xv6v7pvz8skqlzxtdshjp7gux6xxtzpfhq6kamayn` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 78 | `pool1nmf4zdsnwszqn2qzx0mqw0q9qh5l02mafylq6qjd2kf2qftzkuz` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks; Sep data shared in October, counted for September; Relay in Singapore: 35.240.247.32, the pool's only on-chain relay (ip-api.com, 2026-10-19) |
| 79 | `pool1nxpv45mgx6jdx5d4ldpj0rgtq5l839xk8crpy0zqspkk7c6x54a` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 80 | `pool1p8fwflysf9tkq3tnmplfevswzszfh0pwx80q5yhy6jlcx8fuwwx` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 81 | `pool1pkhuhpjrfdufmdfsulpd6j862r4c02ppfzugtv9vxultxw30lvr` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 82 | `pool1qdkwyr0umcrc5vjquhe498qh74z3wz9ty6dg360y7evn7r478nu` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 83 | `pool1qpk543ymtnegdpvz58jzrfsszrshmhwawjpuxk8t4ckexr7ghcz` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 84 | `pool1qvh8lse5mathpl7etl2cpczjqag8ye9lpsmehmpcww2wyn37eha` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Aug: shared relay 109.228.52.195:3010 with pool1gfgvkyd… for 1.5 h; relay 109.228.52.195:3010 with pool15svjdp7… for 0.1 h, under the 48-hour limit; no deduction |
| 85 | `pool1r6csfcpf3ka5en45999cz2s6dg3nznfxqpuwzzt6vresgus6qwa` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Aug: shared relay musashi.happystaking.io:3005 with pool1cp8dkjh… for 44 h, under the 48-hour limit; no deduction |
| 86 | `pool1r9fffsytc2ukplarl755pvpplvfayy7m6024zkm50zp8w8yuztj` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 87 | `pool1rwlrxaw36ktxrrrjj27rmdtgqpsapq89er2atjrjzmylje2ttga` | ✅ | ✅ | ❌ | ✅ | ❌ | 100 | Aug: blocks only on Aug 1-10, before the network reset, so not for most of the month; Sep: data shared was from another network |
| 88 | `pool1sel5uajsqarzq6krkwgdxvzfr9qf5nzv4l5t2tfj00nagsw2trk` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 89 | `pool1sfn4qayjll6lq83pv2uzfqx2756fdukj230uv724wqjnu4uktd0` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 90 | `pool1snza9wtxrf7pxpfgpzazweuf90st7at6rvaxqpz2nnr07pvv764` | ✅ | ❌ | ❌ | ✅ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no Metsuke data |
| 91 | `pool1sur7v2wck9x6h5lnan5fakycwwwkej7c9wmffdpqceyl795h0fj` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no blocks |
| 92 | `pool1trscjhwvklhj90dsfar3xlhapf7wqzvfsuh335dy2rzxvnd9awt` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 |  |
| 93 | `pool1u0futpww5ddgt4z7xpt0z2dy6e2047205l6v4ks485fm7gh53pf` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 94 | `pool1u28z5893zsfk8anj40t62qsr4tvd89vg9r6ajj54urumc6pvuu7` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 95 | `pool1ucmwhkvxzp38zhqt3mc3ymjdzztrrlzeu84v3h542ygag5h2shl` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 96 | `pool1ucwmpkjmnu6n43was0gat4nd5suldvp6u3rxkn9rthg8v7ek4mf` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 |  |
| 97 | `pool1uhjg5p9hczv9pjj4rzfm0xlj25exkyv8t6rteeedfgs7zskvm79` | ✅ | ❌ | ❌ | ✅ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no Metsuke data |
| 98 | `pool1uk72a239s59mrj4n8rypsq0mwmffchp6vvnznqay22mlzxkfzu6` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Relay in Singapore: 89.233.105.53, the pool's only on-chain relay (ip-api.com, 2026-10-19) |
| 99 | `pool1uwhyem2njw2x7er0n334xp367ghqa8j0s5gp4d7wtdd66t7xdaq` | ✅ | ❌ | ✅ | ✅ | ❌ | 100 | Jul: no blocks; Sep: no Metsuke data |
| 100 | `pool1v4v09p5d9esn5ltrzq8j0q4gk7h2s2k8mgz80cs6ghewy60wvew` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 101 | `pool1vgylvtu255k0gt82fev8aq00q6rwjesw7usjckgn5vdtwy3x0ls` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 102 | `pool1vlthv7cp6fjz6rf4t7azq25tuwd0hnsvnn0uath62y736w5qns3` | ✅ | ❌ | ❌ | ✅ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no Metsuke data |
| 103 | `pool1vrnkhhhxs0zmjk0t2s8huryh4avaua08u08njjtkappyywzhull` | ✅ | ❌ | ✅ | ✅ | ✅ | 0 | Jul: no blocks; Aug: shared relay 62.84.177.82:3010 with pool1zfeup8l… for 161 h; relay 62.84.177.82:3010 with pool1g9h4y4x… for 161 h, over the 48-hour limit; not paid, pool1zfeup8l… paid instead as the pool with most blocks; Sep data shared in October, counted for September; Sep: shared relay 62.84.177.82:3010 with pool1zfeup8l… for 228 h; relay 62.84.177.82:3010 with pool1g9h4y4x… for 228 h, over the 48-hour limit; not paid, pool1zfeup8l… paid instead as the pool with most blocks |
| 104 | `pool1wafe9mwmuaqenxkvrtdet6jneg85etsdrcag90q3fnlrqjup30r` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 105 | `pool1wddfg8rnn3s8k3df9uv0tf4llzlxy76zlms6cre6vmnp57qj6dj` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 106 | `pool1wkcjyyz8hazvucnjc5d3j7rlrpa9y0w2ru067t0p5ysljwyz80g` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 107 | `pool1wvnc8lpw8jzktrf5n4k0sjtxsjp4dmskef75tr9dexf7j9px9m7` | ✅ | ❌ | ✅ | ❌ | ❌ | 100 | Jul: no blocks; Sep: no blocks; Sep: shared relay relay1.lvlup-stakepool.com:3101 with pool1397v006… for 223 h, over the 48-hour limit; no deduction, as at most one of the pools qualified that month |
| 108 | `pool1x2gjsp25uhy5s77n2atsxh2kf3n6q0u9pmjn40pgw9jdjwd60z0` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 109 | `pool1x2kqpeaslzp7w84d70dc5sh28c6ej5mf70re708hae9vg4v97az` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks |
| 110 | `pool1x4qc7wuqa8r5l7p9q49l68q4xl38upq53j83p8psylwpudlvnac` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Sep data shared in October, counted for September |
| 111 | `pool1xal6snplnk0zfus8zc3454knvyvv83443h3pnf8usu6hxu4h568` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 112 | `pool1xkypytpkyncn7dnmnhvqtj5q8mrpeef0tqrecudwkrftyzwlwnr` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 113 | `pool1xudqxhpzw4ysqzaz7qh9mm6yhq2n2ytz2c6tyhmz4f80qc8l5f7` | ✅ | ✅ | ✅ | ✅ | ❌ | 200 | Sep: data shared was from another network |
| 114 | `pool1y35689a6wrlrqgrm892v3255ulmm2wwn3kxgd6lp4lepv6mmfsm` | ✅ | ✅ | ✅ | ✅ | ✅ | 300 |  |
| 115 | `pool1y43ykap27aqkg4v8vcnhtf9wj6gwquaj793fkupt5xwsyarv0wl` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 116 | `pool1yezmm2y8thts9xfv29nyj5ns200r4lx6wlc8ckz2ra79kj5zah3` | ✅ | ✅ | ✅ | ✅ | ❌ | 200 | Sep: no Metsuke data |
| 117 | `pool1yhqrvnu6n935n4wu99mfjavc6htc70l0sfyjj9mn43lzc32vq5h` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 118 | `pool1ylvm3dapszd2lvyn6d2kd0c5swfhtkrz4fea8v8qe7glge2hda0` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 119 | `pool1za7357m9wvxs7rpnfdy37jv3hlup0xswapnrw67qrveycx03spcb` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no blocks |
| 120 | `pool1ze5yvl9gmzg5rxwzuzvvdz4vtclmqy5fdujvugm09sjg64ufwqt` | ❌ | ❌ | ❌ | ❌ | ❌ | 0 | KYC not completed |
| 121 | `pool1zfeup8ljzutv584um75vqjsr75jx3cr6zkm9xm42empl67yfw8f` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; Aug: shared relay 62.84.177.82:3010 with pool1vrnkhhh… for 161 h; relay 62.84.177.82:3010 with pool1g9h4y4x… for 161 h, over the 48-hour limit; paid as the pool with most blocks, pool1vrnkhhh…, pool1g9h4y4x… not paid; Sep: shared relay 62.84.177.82:3010 with pool1vrnkhhh… for 228 h; relay 62.84.177.82:3010 with pool1g9h4y4x… for 709 h, over the 48-hour limit; paid as the pool with most blocks, pool1vrnkhhh…, pool1g9h4y4x… not paid |
| 122 | `pool1zmgyrcwsvxq84g7yt4w9fjwj4g52njvtu96xt28rqmvzs5k5q64` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks |
| 123 | `pool1zqfgscenna07ww6ap7njpd2k6a33vdkyz8vp2thjptn6vskkq2p` | ✅ | ❌ | ❌ | ❌ | ❌ | 0 | Jul: no blocks; Aug: no blocks; Sep: no blocks; Sep: shared relay 169.58.237.170:3010 with pool189awmny… for 88 h, over the 48-hour limit; no deduction, as at most one of the pools qualified that month |
| 124 | `pool1zzsd237g2cdha6t66cw3qw23mskgzgfu9m58s96hmg7mjfdxjct` | ✅ | ✅ | ✅ | ❌ | ❌ | 200 | Sep: no blocks |
| 125 | `pool1397v0069avr0nyp5fn93qlx6jme8tzknkl0gg9guzwmtg8d7454` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks; Sep: shared relay relay1.lvlup-stakepool.com:3101 with pool1wvnc8lp… for 223 h, over the 48-hour limit; no deduction, as at most one of the pools qualified that month; allow-list* |
| 126 | `pool15l4n58g927s4a9699y8c2zrhpj0gdne2unvrpf8zppla6k0gq24` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; allow-list* |
| 127 | `pool17hcgfm432wv24yw6ud3ace4kss6tl0hfj4xem9hghq4lkf7wmzg` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks; allow-list* |
| 128 | `pool185ztd8nkckvdjtt824ex9kvchrldve8v68d7vd5kgjcjczl4g2c` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks; allow-list* |
| 129 | `pool1as25z5l0rf0spxv9rggrhygttd9hzjr0qr55us0h7xggzq88snn` | ✅ | ❌ | ❌ | ✅ | ✅ | 100 | Jul: no blocks; Aug: no blocks; allow-list* |
| 130 | `pool1knhsdlg3zjkkyhnwaspfy574qulfq0m35ygvtaa5adh95m4hzjc` | ✅ | ❌ | ✅ | ✅ | ✅ | 200 | Jul: no blocks; allow-list* |

</div>

---

## Notice and review procedure

The figures above are the Musashi team's calculation of rewards earned under the MusashiNet Testnet Reward Program Terms and Conditions for participation in July, August and September 2026. They are based on the on-chain and data-sharing records available to us at the time of calculation. Publication of this table does not by itself constitute an obligation to pay any amount, and all payments remain subject to the Terms and Conditions, including the identity verification and wallet check requirements.

If you disagree with any figure relating to a pool you registered, you must send a written request for review no later than 23:59 UTC on 22 October 2026 to [carlos.lopezdelara@iohk.io](mailto:carlos.lopezdelara@iohk.io). The request must be sent from the same email address you used to register for the program, so that we can verify it, and should identify the pool ID or IDs concerned, the month or months in question, and the grounds for your disagreement, with any supporting evidence. We will review each request against the relevant records and respond to you by email. Where the review shows an error, we will correct the figures accordingly. Requests received after 23:59 UTC on 22 October 2026 will not be considered, and the figures for any pool not subject to a timely request will be treated as final.
