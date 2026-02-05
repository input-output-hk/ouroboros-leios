# Cardano Script Mapping

Identification of high-activity Plutus scripts by MEV relevance. Data sourced from on-chain redeemer counts.

| Version | Date       | Scripts Mapped |
|---------|------------|----------------|
| 0.1     | 2026-02-05 | 59 scripts     |

## Summary

| Category | Scripts | Redeemers | % of Top 100 |
|----------|---------|-----------|--------------|
| DEX      | 18      | 21.0M     | 61%          |
| NFT      | 4       | 8.0M      | 23%          |
| Unknown  | 6       | 5.4M      | 16%          |

## Top Scripts by Activity

| Rank | Script Hash | Protocol | Category | Contract Type | MEV Risk | Redeemers |
|------|-------------|----------|----------|---------------|----------|-----------|
| 1 | `a65ca58a4e9c755fa830173d2a5caed458ac0c73f97db7faae2e7e3b` | Minswap | DEX | V1 Order Validator | HIGH | 5.0M |
| 2 | `9068a7a3f008803edac87af1619860f2cdcde40c26987325ace138ad` | JPG Store | NFT | V2 Contract | MEDIUM | 4.5M |
| 3 | `e1317b152faac13426e6a83e06ff88a4d62cce3c1634ab0a5ec13309` | Minswap | DEX | V1 Pool Validator | HIGH | 4.0M |
| 4 | `4a59ebd93ea53d1bbf7f82232c7b012700a0cf4bb78d879dabb1a20a` | NFT Marketplace | NFT | Sales/Escrow | MEDIUM | 2.6M |
| 5 | `ea07b733d932129c378af627436e7cbc2ef0bf96e0036bb51b3bde6b` | Minswap | DEX | V2 Pool Validator | HIGH | 1.5M |
| 6 | `464eeee89f05aff787d40045af2a40a83fd96c513197d32fbc54ff02` | Splash | DEX | Order Contract | HIGH | 1.7M |
| 7 | `0237cc313756ebb5bcfc2728f7bdc6a8047b471220a305aa373b278a` | WingRiders | DEX | Shares Lock V2 | HIGH | 1.6M |
| 8 | `c3e28c36c3447315ba5a56f33da6a6ddc1770a876a8d9f0cb3a97c4c` | Minswap | DEX | V2 Order Validator | HIGH | 1.8M |
| 9 | `96f5c1bee23481335ff4aece32fe1dfa1aa40a944a66d2d6edc9a9a5` | Unknown | Staking? | Reward Validator | LOW | 1.5M |
| 10 | `1eae96baf29e27682ea3f815aba361a0c6059d45e4bfbe95bbd2f44a` | Minswap | DEX | Pool Batching Stake | HIGH | 1.4M |
| 11 | `a55f409501bf65805bb0dc76f6f9ae90b61e19ed870bc00256813608` | Unknown | DeFi? | Unknown Spend | HIGH | 1.3M |
| 12 | `ba158766c1bae60e2117ee8987621441fac66a5e0fb9c7aca58cf20a` | SundaeSwap | DEX | V1 Order Validator | HIGH | 1.1M |
| 13 | `c727443d77df6cff95dca383994f4c3024d03ff56b02ecc22b0f3f65` | JPG Store | NFT | V3 Marketplace Ask | MEDIUM | 826K |
| 14 | `4020e7fc2de75a0729c3cc3af715b34d98381e0cdbcfa99c950bc3ac` | SundaeSwap | DEX | V1 Pool Validator | HIGH | 812K |
| 15 | `905ab869961b094f1b8197278cfe15b45cbe49fa8f32c6b014f85a2d` | Unknown | DeFi? | Unknown Spend | MEDIUM | 770K |
| 16 | `86ae9eebd8b97944a45201e4aec1330a72291af2d071644bba015959` | WingRiders | DEX | V1 Order Validator | HIGH | 670K |
| 17 | `646ad13fb9e22d3b802049d85e95dc04edb6471eaa9237a932d38d49` | Unknown | DeFi? | Unknown Spend | MEDIUM | 590K |
| 18 | `e0302560ced2fdcbfcb2602697df970cd0d6a38f94b32703f51c312b` | SundaeSwap | DEX | V3 Pool/Order | HIGH | 428K |
| 19 | `e6c90a5923713af5786963dee0fdffd830ca7e0c86a041d9e5833e91` | WingRiders | DEX | V1 Pool Validator | HIGH | 547K |
| 20 | `00fb107bfbd51b3a5638867d3688e986ba38ff34fb738f5bd42b20d5` | MuesliSwap | DEX | Orderbook V4 | HIGH | 376K |
| 21 | `cb684a69e78907a9796b21fc150a758af5f2805e5ed5d5a8ce9f76f1` | Unknown | DeFi? | Unknown Spend | HIGH | 366K |

## DEX Breakdown

| Protocol | Scripts | Redeemers | % of DEX |
|----------|---------|-----------|----------|
| Minswap | 5 | 13.8M | 62% |
| WingRiders | 3 | 2.8M | 13% |
| SundaeSwap | 4 | 1.9M | 9% |
| Splash | 1 | 1.7M | 8% |
| MuesliSwap | 1 | 0.4M | 2% |

## MEV Risk Classification

| Level | Criteria | Examples |
|-------|----------|----------|
| **HIGH** | DEX orders/pools, liquidation triggers | Minswap orders, SundaeSwap pools |
| **MEDIUM** | NFT marketplaces, oracle-dependent | JPG Store listings |
| **LOW** | Staking, governance, minting | Reward validators |

## Tools

- [UPLC Analyzer](https://uplc.pages.dev) — Decode and inspect script bytecode
- Script data query via Koios API

## Sources

- [StricaHQ Script Registry](https://github.com/ADAOcommunity/cardano-plutus-script-registry)
- [SundaeSwap GraphQL API](https://api.sundae.fi/graphql)
- Protocol documentation and GitHub repositories
