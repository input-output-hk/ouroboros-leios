# Ouroboros Leios

Ouroboros Leios is an optimistic consensus protocol for Cardano that substantially increases transaction throughput while maintaining the security properties of Ouroboros Praos. Block producers create larger secondary blocks referencing additional transactions alongside standard Praos blocks, making use of the computational and bandwidth resources that Praos leaves underutilised. These secondary blocks undergo committee validation before ledger inclusion. Building on years of [research](https://iohk.io/en/research/library/papers/high-throughput-blockchain-consensus-under-realistic-network-assumptions/), the project is transitioning from R&D into engineering with active prototyping against `cardano-node`.

Browse the [project website](https://leios.cardano-scaling.org) for an accessible overview, follow progress on the [roadmap and tracker](https://github.com/orgs/input-output-hk/projects/167), watch [monthly review recordings](https://www.youtube.com/playlist?list=PLnPTB0CuBOBzWWpnojAK3ZaFy9RdofP6l), or join [GitHub Discussions](https://github.com/input-output-hk/ouroboros-leios/discussions) and `#leios` on the IOG [Discord](https://discord.gg/Bc6ABMS3). See [CONTRIBUTING.md](CONTRIBUTING.md) for how to get involved.

## Protocol specification

The protocol is specified in [CIP-0164](https://github.com/cardano-foundation/CIPs/pull/1078) as a response to [CPS-0018](https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md). A machine-checked [formal specification in Agda](https://github.com/input-output-hk/ouroboros-leios-formal-spec) complements the CIP. The [Leios design document](docs/leios-design/README.md) bridges the specification and a `cardano-node` implementation, and the [impact analysis](docs/ImpactAnalysis.md) derives requirements from the protocol design.

## Research and analysis

Two technical report snapshots capture the R&D trajectory: [report 1](docs/technical-report-1.md) (~February 2025) and [report 2](docs/technical-report-2.md) (~August 2025). A [cost analysis](https://leios.cardano-scaling.org/cost-estimator) is available on the website.

[post-cip/](post-cip/) collects findings made after the CIP was submitted — a Markovian model of Linear Leios, UTxO set and lifetime analysis, CPU cost measurements of ledger operations, and mempool and constraint modelling. [analysis/](analysis/) contains simulation experiment results, [DeltaQ modelling of Linear Leios](analysis/deltaq/linear-leios/), bandwidth measurements, and network timing analysis.

## Simulations

The repository contains two independent simulations of the Leios protocol, each with its own README covering build instructions, configuration parameters, and Docker usage.

[sim-rs/](sim-rs/) is a high-performance Rust simulation producing JSONL or CBOR traces and is the actively maintained simulation. [simulation/](simulation/) is an earlier Haskell simulation with built-in Gtk+ visualisation; it predates the move away from input blocks and is no longer up to date with the current protocol design. Both read shared topology and configuration files from [data/](data/).

Traces from either simulation can be explored in the [web-based visualiser](ui/), which also supports live streaming from a running network via Loki. Docker images for both simulations are built from the root [Dockerfile](Dockerfile).

## Demo

The [demo/](demo/) directory collects network-level demonstrations built from prototype `cardano-node` branches, including a Leios-enabled devnet. See [demo/README.md](demo/README.md) for details and links to the prototype branches.

## Cryptographic benchmarks

[crypto-benchmarks.rs/](crypto-benchmarks.rs/) contains a Rust reference implementation and benchmarks of the BLS cryptography used for Leios voting and certificates, including a CLI for testing the full vote-to-certificate pipeline.

## DeltaQ network analysis

[delta_q/](delta_q/) provides a general-purpose web-based tool for modelling network performance using Delta-QSD theory, including extensions for load analysis and gossip diffusion — see the [DeltaQ README](delta_q/README.md) for building and usage. The more recent [analysis/deltaq/linear-leios/](analysis/deltaq/linear-leios/) applies DeltaQ specifically to Linear Leios, computing EB diffusion statistics and certification probabilities.

## Community and governance

Development is tracked on the [project board](https://github.com/orgs/input-output-hk/projects/167) and discussed in [monthly review calls](https://www.youtube.com/playlist?list=PLnPTB0CuBOBzWWpnojAK3ZaFy9RdofP6l). Contributions are welcome — see [CONTRIBUTING.md](CONTRIBUTING.md) and the [Code of Conduct](CODE-OF-CONDUCT.md).
