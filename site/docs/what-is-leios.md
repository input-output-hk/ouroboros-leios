# What is Leios

Ouroboros Leios (Leios) is a research and development project from Input Output designed to make Cardano faster, more scalable, and ready for broader adoption. It is part of the Ouroboros family of consensus protocols, which underpin Cardano’s proof-of-stake (PoS) blockchain.

## What Leios offers

-   **Scalability**: optimizes network bandwidth for faster transaction processing, significantly enhancing Cardano’s scalability. Transactions are confirmed with minimal delays, providing a seamless user experience.
-   **Security**: preserves Ouroboros’ strong security properties with robust defenses against attacks while ensuring fair participation.
-   **Decentralization**: increases throughput by up to 50× without compromising decentralization. The network retains resilience, fairness, and accessibility for all participants.
    
## Why it matters

Cardano’s current protocol, Ouroboros Praos, is secure and decentralized, but sequential block production limits throughput. While nodes and network resources are sufficient, much of the system remains idle during block propagation, keeping transactions per second (TPS) low (~3.5 TPS on mainnet).

Leios addresses these limitations by redesigning the blockchain structure to allow parallel block processing. Early simulations suggest potential throughput targets of over 1,000 TPS, enabling applications such as decentralized finance (DeFi) platforms, non-fungible token (NFT) marketplaces, and online tools to run smoothly at scale.

Leios is part of the broader Ouroboros family of protocols:

-   **Ouroboros Praos**: the current Cardano protocol, providing robust security and decentralization. Sequential block production constrains throughput.
-   **Ouroboros Peras**: a proposed modular upgrade to Praos that improves efficiency and adaptability. Peras acts as an intermediate step, making the protocol more flexible and laying the groundwork for future scalability solutions.
-   **Ouroboros Leios**: a scalability-focused extension that builds on PoS principles while enabling parallel block processing. It remains in research and development and is not yet live on mainnet.
    
### From research to reality

The published [Leios CIP](https://github.com/cardano-foundation/CIPs/pull/1078) represents a strategic balance between performance gains and ecosystem compatibility. The specification targets a 30-50× throughput increase (from ~4.5 TxkB/s to ~140–300 TxkB/s) while keeping latency and network changes manageable. Unlike the original research, which achieves higher throughput but requires extensive ecosystem adjustments and 2–3 minute confirmation times, the CIP strikes a practical compromise:

-   Latency increases modestly (45–60 seconds vs 20 seconds)
-   Transaction structures remain familiar, supporting ecosystem compatibility
-   Deployment is realistic within 1–1.5 years, compared with 2.5–3 years for higher-concurrency alternatives.

<img
  src="/img/research-graphic.svg"
  alt="From research to reality graphic"
  style={{ display: "block", margin: "0 auto", maxWidth: "100%", height: "auto" }}
/>

By situating Leios within the context of Praos and Peras and outlining these strategic trade-offs, it becomes clear that Leios is a deliberate step toward scaling Cardano without compromising its security, decentralization, or ecosystem usability.

## How it works

Ouroboros Leios achieves higher transaction throughput by allowing block producers to create additional blocks alongside the regular Praos chain. These supplementary blocks ([EBs](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#endorser-blocks-ebs)) reference extra transactions that would otherwise wait for the standard Praos blocks ([RBs](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#ranking-blocks-rbs)) in future active slots.

To ensure data availability and correctness, EBs undergo [committee validation](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#step-3-committee-validation) before their transactions are added to the permanent ledger. The key insight is that Leios can maintain Praos’s security guarantees while processing more transactions by carefully controlling when and how these additional blocks are validated and included in the chain.

EB inclusion is opportunistic rather than guaranteed, depending on the random timing of block production relative to the certification process. This approach preserves the existing Praos chain structure while adding substantial transaction capacity through the secondary validation pathway.

<img
  src="/img/how-leios-works-graphic.svg"
  alt="How Leios works protocol timing graphic"
  style={{ display: "block", margin: "0 auto", maxWidth: "100%", height: "auto" }}
/>
