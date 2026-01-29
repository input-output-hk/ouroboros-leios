# MEV Mitigation Approaches

Potential mitigation strategies for MEV in Linear Leios. For attack analysis, see the [attack vectors](./attack-vectors/).

## Overview

| Category | Approach | Layer | Complexity |
|----------|----------|-------|------------|
| [Ordering](#ordering-based) | Random ordering | Batcher/Protocol | Medium |
| [Ordering](#ordering-based) | Batch clearing (uniform price) | Batcher | Medium |
| [Privacy](#privacy-based) | Encrypted/private mempools | Network | High |
| [Privacy](#privacy-based) | Commit-reveal schemes | Protocol | Medium |
| [Economic](#economic) | MEV redistribution | Protocol | High |
| [Economic](#economic) | Inclusion incentives | Protocol | Medium |

---

## Ordering-Based

### Random Ordering

Replace FIFO batcher ordering with randomized selection using a verifiable randomness beacon.

**Mechanism**: Orders within a time window are shuffled using on-chain randomness before execution.

| Pros | Cons |
|------|------|
| Eliminates positional advantage | Requires trusted/verifiable randomness source |
| Simple conceptually | Fairness verification becomes harder |
| Easy to implement at batcher level | Doesn't prevent block producer MEV |

**Production Examples**:
- [Chainlink VRF](https://chain.link/vrf) - verifiable randomness for smart contracts

### Batch Clearing (Uniform Price)

Instead of sequential order execution, calculate a single clearing price for all orders in a batch.

**Mechanism**: Aggregate all buy/sell orders, find equilibrium price, settle everyone at that price.

| Pros | Cons |
|------|------|
| Eliminates ordering advantage entirely within batch | More complex settlement logic |
| Fairer price for all participants | May not suit all order types |
| No information leakage from order sequence | Requires sufficient batch size for efficiency |

**Production Examples**:
- [CoW Protocol](https://cow.fi/) - batch auctions with uniform clearing price on Ethereum
- [Penumbra](https://penumbra.zone/) - batch swaps with private minting

---

## Privacy-Based

### Encrypted/Private Mempools

Route transactions through private channels to trusted block producers.

**Mechanism**: Users submit encrypted txs or use trusted relayers; decrypted only at inclusion time.

| Pros | Cons |
|------|------|
| Proven effective (95% of ETH DEX volume uses this) | Trust assumption on operators |
| Immediate protection for users who opt in | Centralizing tendency |
| Compatible with existing protocols | Doesn't prevent producer MEV |

**Production Examples**:
- [Flashbots Protect](https://protect.flashbots.net/) - private tx submission, prevents sandwich attacks
- [MEV Blocker](https://mevblocker.io/) - by CoW Protocol, rebates users for MEV extracted
- [MEV Share](https://docs.flashbots.net/flashbots-mev-share/overview) - lets users capture portion of MEV from their txs
- [Shutter Network](https://shutter.network/) - threshold encryption for front-running protection
- [Bloxroute](https://bloxroute.com/) - private transaction relaying infrastructure

### Commit-Reveal Schemes

Users commit to transaction hash first, reveal contents later.

**Mechanism**: Two-phase submission where commitment is included before reveal.

| Pros | Cons |
|------|------|
| No trusted third party | Increases latency (2 blocks minimum) |
| Cryptographically secure | Failed reveals waste blockspace |
| Can be implemented at protocol level | Complex UX |

**Examples**:
- [Submarine Sends](https://libsubmarine.org/) - research library for hiding tx content
- [SUAVE](https://writings.flashbots.net/the-future-of-mev-is-suave) - Flashbots' next-gen MEV architecture (research)

---

## Economic

### MEV Redistribution

Capture MEV at protocol level and redistribute to affected users or public goods.

**Mechanism**: Auction block production rights; surplus distributed to stakers or burned.

| Pros | Cons |
|------|------|
| Aligns incentives | Complex mechanism design |
| Funds public goods | May not eliminate MEV, just redirect it |
| Reduces race-to-bottom dynamics | Requires significant protocol changes |

**Production Examples**:
- [Flashbots MEV-Boost](https://boost.flashbots.net/) - separates block building from proposing, ~90% of ETH blocks
- [Proposer-Builder Separation (PBS)](https://ethereum.org/en/roadmap/pbs/) - Ethereum's long-term MEV strategy
- [Arbitrum Timeboost](https://docs.arbitrum.io/how-arbitrum-works/timeboost/gentle-introduction) - sealed-bid auction for priority access
- [Jito](https://www.jito.wtf/) - MEV redistribution on Solana, returns value to stakers
- [Skip Block SDK](https://github.com/skip-mev/block-sdk) - MEV lanes for Cosmos chains

### Inclusion Incentives

Penalize censorship and reward timely inclusion.

**Mechanism**: Track transaction submission times; reward producers for prompt inclusion.

| Pros | Cons |
|------|------|
| Reduces censorship MEV | Requires reliable submission timestamps |
| Encourages honest behavior | Gaming potential |
| Can be tuned via parameters | Doesn't address ordering MEV |

**Production Examples**:
- [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559) - base fee mechanism reduces fee manipulation
- [Inclusion Lists](https://ethereum.org/en/roadmap/#single-slot-finality) - proposed for Ethereum to force tx inclusion
- [FOCIL](https://ethresear.ch/t/fork-choice-enforced-inclusion-lists-focil) - fork-choice enforced inclusion lists (research)

---

## Leios-Specific Considerations

| Leios Feature | MEV Implication | Mitigation Fit |
|---------------|-----------------|----------------|
| EB construction opaque until announcement | Producer has private ordering window | Commit-reveal at EB level |
| L<sub>vote</sub> observation window | Network learns EB contents before finality | Shorter L<sub>vote</sub> or encrypted EBs |
| RB-only bypass (T19) | High-value txs avoid EB exposure | Economic incentives for EB usage |
| 75% voting quorum | Distributes power | Already mitigates collusion |
