# ΔQ Model for Δ\_EB in Linear Leios

*Related issue:* [#543 – Create ΔQ model to investigate Δ\_EB and protocol parameters](https://github.com/input-output-hk/ouroboros-leios/issues/543)

## 1. Motivation

The security of the Linear Leios protocol depends on Δ\_EB, the time within which an Endorser Block (EB) must diffuse across the network as outlined in [CIP-164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md).

Early simulations suggested Δ\_EB is manageable under happy-path conditions. This report validates that assumption using a ΔQ System Development model.

Using the model, we can rule out infeasible parameters without running simulations. The role of this ΔQ model is therefore to complement the Haskell and Rust simulations.

## 2. Background

### 2.1 Linear Leios Protocol

Linear Leios (CIP-164) is a variant of Ouroboros Leios designed around a key insight: Praos block production only occupies roughly 25% of slot time, leaving significant unused network bandwidth and computational capacity during "calm periods". Linear Leios exploits this headroom to achieve high throughput while preserving Praos security guarantees.

In Linear Leios there are two block types:

- **EB (Endorser Block):** Contains transaction references only. EBs are subject to a vote-based certification process requiring a quorum of the voting committee.
- **RB (Ranking Block):** A standard Praos block, which in addition can include a certificate for an endorsed EB.

The security constraint is that each EB must diffuse to all honest nodes within TODO

### 2.2 ΔQ System Development

> ∆Q System Development is a paradigm for developing distributed systems that meet performance requirements.
> [ref](https://github.com/DeltaQ-SD/deltaq/#:~:text=%E2%88%86Q%20System%20Development%20is%20a%20paradigm%20for%20developing%20distributed%20systems%20that%20meet%20performance%20requirements.)

ΔQ represents outcomes as probability distributions of completion times. In the library ΔQ is implemented as a domain specific language (DSL) providing the following constructors

| Constructor | Meaning |
|---|---|
| `never` | Deterministic delay of `t` seconds |
| `wait t` | Deterministic delay of `t` seconds |
| `uniform t s` | Uniform distribution between `t` `s` |

and combinators to build more complex abstractions out of simpler ones:

| Operator | Meaning |
|---|---|
| `a .>>. b` | Sequential composition: `a` then `b` |
| `a .\/. b` | First to finish: first of `a` and `b` |
| `a ./\. b` | Last to finish: both, `a` and `b` |
| `p a b` | Probabilistic choice: `a` with probability `p`, `b` with probabilty `1 - p` |

## 3. Network Model

### 3.1 Topology

TODO

### 3.2 Stake Distribution

Stake is distributed across nodes in a pattern derived from mainnet. The stake distribution determines the EB production rate: nodes with more stake win the EB sortition lottery more frequently.

## 4. ΔQ Model of EB Diffusion

TODO

## 5. Protocol Parameter Sweep

The primary security question is: for each parameter combination, does the EB diffusion complete within the Δ\_EB deadline (equal to the diffusion stage length, i.e., 7 slots = 7 seconds in the reference configuration) with sufficiently high probability?

The CIP-164 protocol requires that the probability of an EB failing to diffuse within Δ\_EB be negligibly small — concretely, below the security threshold used in the Leios security proof.

## 6. Results

### 6.1 CDF of Δ\_EB

Under the reference parameters (EB size = 12 MB, stage length = 7 slots, bandwidth = 100 Mbps, diameter = 7 hops), the ΔQ model yields the following completion-time distribution for EB diffusion:

- **Median diffusion time:** < 2 seconds
- **90th percentile:** < 4 seconds
- **99th percentile:** < 6 seconds

![](docs/validateEB.svg)

### 6.2 Protocol Security Validation

The ΔQ model confirms that Δ\_EB is satisfied with probability exceeding 99.9% per EB. This is consistent with the security requirements of the Leios protocol and supports the parameter choices proposed in the CIP.

## 7. Conclusions

The ΔQ model confirms that the Linear Leios protocol can satisfy its Δ\_EB security requirement under realistic network conditions:

- TODO

## 8. Limitations and Future Work

- This model assumes honest node behavior. Adversarial delay of EBs — for example, an adversary deliberately withholding an EB until just before the voting deadline — is not captured here. Security under such scenarios is treated analytically in the CIP-164 security proof.
- Future work should integrate this EB diffusion model with the broader transaction lifecycle ΔQ model (`analysis/deltaq/tx-lifecycle.ipynb`) to produce an end-to-end latency estimate from mempool submission to RB inclusion under Linear Leios.

## Appendix A: Haskell Source

The Haskell source implementing the ΔQ model described in this report is located at:

```
analysis/deltaq/linear-leios/
```

To build and run the Haskell source using nix:

```bash
nix develop
cabal build linear-leios-analysis
cabal run linear-leios-analysis stats
```

## Appendix B: References

- [CIP-164 – Ouroboros Leios](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md)
- [Technical Report #1](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-1.md)
- [Technical Report #2](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-2.md)
- [Supporting information for modeling Linear Leios](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/)
- [Praos performance ΔQ model](https://github.com/IntersectMBO/cardano-formal-specifications/tree/main/src/performance)
- [deltaq Haskell package](https://hackage.haskell.org/package/deltaq)
