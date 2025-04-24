---
CIP: "?"
Title: Ouroboros Leios - Greater transaction throughput
Status: Active
Category: One of the registered [categories](#categories) covering one area of the ecosystem.
Authors:
    - 
Implementors: N/A
Discussions:
    - 
Solution-To:
    - CPS-0018
Created: 2025-03-07
License: Apache-2.0
---


## Abstract

> [!NOTE]
>
> A short (\~200 word) description of the proposed solution and the technical issue being addressed.

As Cardano evolves, there will be increasing demand for greater network  
capacity to support new and existing users and applications. The long term  
solution is to rebase Cardano on the new Ouroboros Leios protocol.  
Ouroboros Leios is a new member of the Ouroboros family that is designed  
specifically for high throughput, without compromising security. This will  
meet expected future demands, providing a basis for continuing Cardano growth  
and scalability.

## Motivation: why is this CIP necessary?

> [!NOTE]
> 
> A clear explanation that introduces a proposal's purpose, use cases, and stakeholders. If the CIP changes an established design, it must outline design issues that motivate a rework. For complex proposals, authors must write a [Cardano Problem Statement (CPS) as defined in CIP-9999][CPS] and link to it as the `Motivation`.

Cardano's current throughput (measured both in data rate and available script  
execution time) is adequate for the current demand. There is also some  
opportunity to increase the block sizes and script execution limits to meet  
emerging future demands for increased network capacity. There are however  
fundamental limits to how far the block size and the script execution budget  
can be pushed, while maintaining system security.

Under Ouroboros Praos, in order to ensure the security of the overall system,  
blocks must be distributed across the network reliably in "" time slots.  
This is set to be 5 seconds on the Cardano mainnet. The block relaying process  
is an essentially serial process: blocks must be relayed between consecutive  
block producer nodes through a series of intermediate relay nodes. The overall  
time that this takes is proportional to the number of network hops between one  
block producer and the next, and the network latency of each of those hops  
(which must in general span the whole globe). Given that this must always  
happen within 5 seconds, this puts a hard upper limit on how large each block  
can be and also on how much time can be spent validating transactions and  
scripts.

In order to substantially scale beyond this requires changes to the underlying  
blockchain algorithm. There are significant opportunities to scale: the  
network and CPU resources on most nodes are almost idle much of the time. With  
a different algorithm, these resources can be used to increase the total chain  
bandwidth.
## Specification

> [!NOTE]
> 
> The technical specification should describe the proposed improvement in sufficient technical detail. In particular, it should provide enough information that an implementation can be performed solely based on the design outlined in the CIP. A complete and unambiguous design is necessary to facilitate multiple interoperable implementations.
> 
> This section must address the [Versioning](#versioning) requirement unless this is addressed in an optional Versioning section.
> 
> If a proposal defines structure of on-chain data it must include a CDDL schema.


### Non-normative overview of Leios

> [!IMPORTANT]
> 
> Write this section after the details of the recommended variant of Full Leios have been settled.

### Normative Leios specification in Agda

> [!IMPORTANT]
> 
> Work in progress: https://github.com/input-output-hk/ouroboros-leios-formal-spec/tree/main/formal-spec/Leios.
> 
> - [ ] Do we plan to embed the Agda in this document?
> - [ ] If so, will all of the Agda be embedded, instead of just the core subset?

### Constraints on Leios protocol parameters

| Parameter                      | Symbol        | Units   | Description                                                                 | Constraints                | Rationale                                                    |
| ------------------------------ | ------------- | ------- | --------------------------------------------------------------------------- | -------------------------- | ------------------------------------------------------------ |
| Stage length                   | $L$           | slot    |                                                                             | $L \geq \Delta$            |                                                              |
| Input-block production rate    | $f_\text{IB}$ | 1/slot  |                                                                             | $0 \lt f_\text{IB}$        |                                                              |
| Endorser-block production rate | $f_\text{EB}$ | 1/stage |                                                                             | $0 < f_\text{EB}$          |                                                              |
| Mean committee size            | $n$           | parties |                                                                             |                            |                                                              |
| Quorum size                    | $\tau$        | parties |                                                                             | $\tau > n / 2$             |                                                              |
| . . .                          |               |         |                                                                             |                            |                                                              |
| Network diffusion time         | $\Delta$      | slot    | Upper limit on the time needed to diffuse a message to all nodes.           | $\Delta > 0$               | Messages have a finite delay.                                |
| Praos active slot coefficient  | $f_\text{RB}$ | 1/slot  | The probability that a party will be the slot leader for a particular slot. | $0 \lt f \leq \Delta^{-1}$ | Blocks should not be produced faster than the network delay. |

### Specification for votes and certificates

The next section outlines the requirements for Leios sortition, voting, and certificates. Although these are stringent, several proposed schemes meet the criteria. Ideally, a common Cardano voting infrastructure would be used across Leios, Peras, Mithril, and partner chains. For concreteness, however, this section also documents a BLS approach that is feasible for Leios.

#### Requirements

Leios is flexible regarding the details of votes, certificates, and sortition. The key requirements in this regard follow.

1. *Succinct registration of keys:* The registration of voting keys should not involve excessive data transfer or coordination between parties. Ideally, such registration would occur as part of the already existing operational certificates and not unduly increase their size.
2. *Key rotation:* The cryptographic keys used to sign Leios votes and certificates *do not* need to be rotated periodically because the constraints on Leios voting rounds and the key rotation already present in Praos secure the protocol against attacks such as replay and key compromise.
3. *Deterministic signatures:* Deterministic signatures can guard against attacks that weakening key security. 
4. *Local sortition:* Selection of the voting committee should not be so deterministic and public as to open attack avenues such as denial-of-service or subversion.
5. *Liveness:* Adversaries with significant stake (e.g., more than 35%) should not be able to thwart a honest majority from reaching a quorum of votes for an EB.
6. *Soundness:* Adversaries with near majority stake (e.g., 49%) should not be able to form an adversarial quorum that certifies the EB of their choice.
7. *Small votes:* Because vote traffic is large and frequent in Leios, the votes themselves should be small. Note that the large size of Praos KES signatures precludes their use for signing Leios votes.
8. *Small certificates:* Because Leios certificates are frequent and must fit inside Praos blocks, they should be small enough so there is plenty of room for other transactions in the Praos blocks. Note once again that certificates based on Praos KES signatures are too large for consideration in Leios.
9. *Fast cryptography:* The computational burden of creating and verifying voting eligibility, the votes themselves, and the resulting certificate must be small enough to fit within the CPU budget for Leios stages.

#### BLS certificate scheme

Consider the following voting and certificate scheme for Leios:

1. As part of their operational certificate, stake pools register BLS keys for use in voting and prove possession of those keys.
2. Nodes verify the proofs of possession of the keys they receive.
3. For each epoch, the Fait Accompli[^1] scheme wFA<sup>LS</sup> is applied to the stake distribution in order to determine the *persistent voters* for the epoch.
    1. Persistent voters should vote in every election during the epoch.
    2. A different supplement of *non-persistent voters* are selected at random for each election during the epoch using the *local sortition* algorithm.
5. The certificate records the set of voters, proof of their eligibility, and the quorum achieved.

[^1]: Peter Gaži, Aggelos Kiayias, and Alexander Russell, "Fait Accompli Committee Selection: Improving the Size-Security Tradeoff of Stake-Based Committees," Cryptology ePrint Archive, Paper 2023/1273 (2023), [https://eprint.iacr.org/2023/1273](https://eprint.iacr.org/2023/1273).

##### Key registration

The key registration records the public key and the proof of its possession.

1. The Pool ID (or similar unique identifier) identifies the pool holding the key and comprises 28 bytes.
2. The public key $\mathit{mvk}$ belongs to $\mathbb{G}_2$ , so it occupies 96 bytes if BLS12-381 with compression is used.
3. The proof of possession for the secret key is the pair $\left(H_{\mathbb{G}_1}(\text{``PoP''} \parallel \mathit{mvk})^\mathit{sk}, g_1^\mathit{sk}\right)$, where $\mathit{sk}$ is the secret key and $H$ hashes to points in $\mathbb{G}_1$. This pair will occupy 96 bytes with compression.
4. The KES signature for the above will add another 448 bytes.

Altogether, a key registration occupies $28 + 96 + 2 \times 48 + 448 = 668$ bytes. This registration needs to be recorded on chain so that certificates can be later verified independently. Ideally, the BLS keys would be registered as part of the SPO's *operational certificate*, which is renewed every ninety days.

##### Sortition

Figure 7 of the Fait Accompli paper[^1] provides the algorithm for determining which pools are persistent voters. The inequality for this determination can be computed exactly using rational arithmetic, so there is no danger of round-off errors. The input to the formula is the size of the committee and the distribution of stake among the pools.

The non-persistent pools are subject to local sortition (LS) for each vote, based on an updated stake distribution where the persistent voters have been removed and where the distribution is normalized to unit probability. The VRF value for that sortition is the bytes of the SHA-256 hash of the BLS signature on the election identifier $eid$. The probability that a pool with fraction $\sigma$ of the stake is awarded $k$ votes of the committee of $n$ votes is 

$$
\mathcal{P}(k) := \frac{(n \cdot \sigma)^k \cdot e^{- n \cdot \sigma}}{k!}
$$

This VRF value is used to look up the correct number of votes from the cumulative distribution for $\mathcal{P}(k)$. The same Taylor-series expansion technique used in Praos can handle the irrational arithmetic in a deterministic manner. In practice it is unlikely that the non-persistent pools would ever be awarded more than one vote, so it may be feasible to simply award one vote whenever $k \ge 1$.

Each vote has a weight, measured as stake. A quorum is achieved if the weights of the votes in the certificate exceeds a specified quorum of stake. The weight calculation is also proved in Figure 7 of the aforementioned paper:

- The weight of a persistent voter is simply their stake.
- The each vote cast by a non-persistent voter has weight equal to the non-persistent stake divided by the *expected* number of non-persistent seats on the voting committee.

##### Votes

Votes cast by persistent versus non-persistent voters contain different information because persistent voters can be identified by a two-byte identifier and the do not have to provide an eligibility proof. This amounts to 90 bytes for persistent votes and 164 bytes for non-persistent votes.

- Common to all votes
	- *Election ID:* 8 bytes
	- *Hash of endorser block:* 32 bytes
	- *Vote signature:* 48-byte BLS signature on the election ID and EB hash
- Specific to persistent voters
	- *Epoch-specific identifier of the pool:* 2 bytes
- Specific to non-persistent voters
	- *Pool ID:* 28 bytes
	- *Eligibility signature:* a 48-byte BLS signature on the election ID

##### Certification

Consider the committee size $n$, which contains $m$ persistent voters. The certificate must contain the following information:

- Election and EB
    - *Election ID:* Presumably a 8-byte identifier for the Leios election is included in the certificate, though perhaps this is not strictly necessary. This could just be the slot number.
    - *Message:* the 32-byte hash of the endorser block is also included in the certificate.
- Identity of voters
    - Persistent voters are encoded in a bitset of size $m$, occupying $\left\lceil m / 8 \right\rceil$ bytes.
    - Non-persistent voters are encoded by their Pool ID (or equivalent), occupying 28 bytes each and hence $28 \cdot (n - m)$ bytes total.
    - Alternatively, all possible voters could be assigned bits in a bitset, with size $\left\lceil N_\text{pools} / 8 \right\rceil$.
- Eligibility proof
    - Persistent voters are eligible by definition (by virtue of their stake in the epoch), so no proof is needed.
    - Non-persistent voters prove eligibility with a 48 byte (compressed) BLS signature on the message, occupying $48 \cdot (n - m)$ bytes total.
- Aggregate signatures
    - *Signed message:* This aggregate BLS signature on the message is 48 bytes (compressed).
    - *Signed election proofs:* Perhaps not strictly necessary, but another 48 byte (compressed) BLS signature can attest to the proof of the eligibility, see **BLS.BSig** in the Leios paper[^2].
    
Thus the total certificate size is

$$
\text{certificate bytes} = 136 + \left\lceil \frac{m}{8} \right\rceil + 76 \times (n - m)
$$

but not including any minor overhead arising from CBOR serialization. As noted previously, only a quorum of votes actually needs to be recorded, but the full set might need to be recorded in order for any voting rewards to be computed.

[^2]: Sandro Coretti-Drayton et al., "High-Throughput Blockchain Consensus under Realistic Network Assumptions" (working paper, April 2024), https://iohk.io/en/research/library/papers/high-throughput-blockchain-consensus-under-realistic-network-assumptions/.

### CDDL schema for the ledger

#### IB schema

> [!IMPORTANT]
> 
> Translate the Agda type for input blocks into CDDL.

#### EB schema

> [!IMPORTANT]
> 
> Translate the Agda type for endorser blocks into CDDL.

#### Certificate schema

> [!IMPORTANT]
> 
> Translate the Agda type for certificates into CDDL.

#### RB schema

> [!IMPORTANT]
> 
> Provide the diff for the CDDL for Praos blocks, so that Leios certificates are included.

## Rationale: how does this CIP achieve its goals?

> [!NOTE]
> 
> The rationale fleshes out the specification by describing what motivated the design and what led to particular design decisions. It should describe alternate designs considered and related work. The rationale should provide evidence of consensus within the community and discuss significant objections or concerns raised during the discussion.
> 
> It must also explain how the proposal affects the backward compatibility of existing solutions when applicable. If the proposal responds to a [CPS][], the 'Rationale' section should explain how it addresses the CPS and answer any questions that the CPS poses for potential solutions.

### How Leios increases throughput


### Evidence that Leios provides high throughput


### Why Leios is practical to implement


The feasibility and performance of the cryptographic required for Leios is demonstrated by a prototype implementation[^3] and the benchmarks in the Appendix [Cryptographic benchmarks](#cryptographic-benchmarks). The small size (less than 9 kB) of Leios certificates is documented in the Appendix [Certificate size for realistic stake distributions](#certificate-size-for-realistic-stake-distributions).

### Use cases


### Feasible values for Leios protocol parameters

The table below documents a set of Leios protocol parameters that provided high throughput and reasonably fast settlement in the prototype Haskell and Rust simulations of Leios. The exact choice of parameters that would be adopted on the Cardano mainnet must be subject to discussion and consideration of tradeoffs.

| Parameter                      | Symbol        | Units    | Description                                                                 | Feasible value | Justification                                                                                                             |
| ------------------------------ | ------------- | -------- | --------------------------------------------------------------------------- | -------------: | ------------------------------------------------------------------------------------------------------------------------- |
| Stage length                   | $L$           | slot     |                                                                             |             10 | Short stages increase settlement speed, but the stage length must be generously larger than the propagation time for IBs. |
| Input-block production rate    | $f_\text{IB}$ | 1/slot   |                                                                             |                |                                                                                                                           |
| Endorser-block production rate | $f_\text{EB}$ | 1/stage  |                                                                             |                |                                                                                                                           |
| Mean committee size            | $n$           | parties  |                                                                             |            500 | Probabilistic analyses of adversarial stake scenarios.                                                                    |
| Quorum size                    | $\tau$        | fraction |                                                                             |            60% | Probabilistic analyses of adversarial stake scenarios.                                                                    |
| . . .                          |               |          |                                                                             |                |                                                                                                                           |
| Praos active slot coefficient  | $f_\text{RB}$ | 1/slot   | The probability that a party will be the slot leader for a particular slot. |           0.05 | This is the current value on mainnet, but it may become feasible to reduce it if Praos blocks are made smaller.           |

The analysis [Committee size and quorum requirement](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-1.md#committee-size-and-quorum-requirement) in the first Leios Technical Report indicates that the Leios committee size should be no smaller than 500 votes and the quorum should be at least 60% of those votes. However, the proposed Fait Accompli[^1] scheme wFA<sup>LS</sup> achieves compact certificates that do not become larger as the number of voters increases, so larger committee sizes might be permitted for broader SPO participation and higher security. The committee size should be large enough that fluctuations in committee membership do not create an appreciable probability of an adversarial quorum when the adversarial stake is just under 50%. The quorum size should be kept large enough above 50% so that those same fluctuations do not prevent an honest quorum, but not so large that a minority adversary can prevent the honest quorum. Larger committees require more network traffic, of course.


### Attack and mitigation


### Resource requirements


## Path to active

> [!NOTE]
> 
> Organised in two sub-sections:

- [ ] Clear evidence of stakeholder use cases that require the high transaction throughput that Leios provides.

### Acceptance criteria

> [!NOTE]
> 
> Describes what are the acceptance criteria whereby a proposal becomes _'Active'_.
> 
> This sub-section must define a list of criteria by which the proposal can become active. Criteria must relate to observable metrics or deliverables and be reviewed by editors and project maintainers when applicable. For example: "The changes to the ledger rules are implemented and deployed on Cardano mainnet by a majority of the network", or "The following key projects have implemented support for this standard".

- [ ] The revised `cardano-node` implementations pass the node-level conformance test suites.
- [ ]  Audit.
- [ ]  Successful operation in testnet environments.
- [ ]  Community agreement on the settings for the Peras protocol parameters.

### Implementation plan

> [!NOTE]
> Either a plan to meet those criteria or `N/A` if not applicable.
> 
> This sub-section should define the plan by which a proposal will meet its acceptance criteria, when applicable. More, proposals that require implementation work in a specific project may indicate one or more implementors. Implementors must sign off on the plan and be referenced in the document's preamble.
> 
> In particular, an implementation that requires a hard-fork should explicitly mention it in its _'Implementation Plan'_.

- [ ]  Detailed node-level (as opposed to this protocol-level) specification.
- [ ]  Develop node-level conformance test suite.
- Consider developing a "quick and dirty" implementation for large scale experiments.
- Coordinate with related activities on other protocol enhancements.
    - Compatibility between Peras, Leios, and Genesis.
    - Common design and implementation for certificates, voting, and related key registration: Mithril, Peras, Leios, and partner chains.
- Triage by intersect Core Infrastructure and Consensus functions.

## Versioning

> [!NOTE]
> 
> if Versioning is not addressed in Specification
> 
> CIPs must indicate how the defined Specification is versioned.  **Note** this does not apply to the CIP text, for which annotated change logs are automatically generated and [available through the GitHub UI](https://docs.github.com/en/pull-requests/committing-changes-to-your-project/viewing-and-comparing-commits/differences-between-commit-views) as a history of CIP files and directories.
> 
> Authors are free to describe any approach to versioning that allows versioned alterations to be added without author oversight.  Stipulating that the proposal must be superseded by another is also considered to be valid versioning.
> 
> A single Versioning scheme can be placed either as a subsection of the Specification section or in an optional Versioning top-level section near the end.  If the Specification contains multiple specification subsections, each of these can have a Versioning subsection within it.


## References

> [!NOTE]
> 
> Optional

- [CPS-18: Greater transaction throughput](https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md)
- [Leios R&D web site](https://leios.cardano-scaling.org/)
- [Leios channel on IOG Discord](https://discord.com/channels/826816523368005654/1247688618621927505)
- [Github repository for Leios R&D](https://github.com/input-output-hk/ouroboros-leios)
- [Github repository for Leios formal specification](https://github.com/input-output-hk/ouroboros-leios-formal-spec)

## Appendices

> [!NOTE]
> 
> Optional


### Cryptographic benchmarks

The following benchmarks for Leios cryptographic operations were computed with Rust code[^3] that uses a reference implementation for BLS operations. A variety of optimizations are possible, so the measurements below should be considered worst-case bounds.

- Sortition
    - *Input blocks:* 230 µs
    - *Endorser blocks:* 230 µs
    - *Persistent voters:* 5.5 ms (once per epoch)
    - *Non-persistent voters:* 230 µs (once per pipeline)
- Vote
    - *Verify the proof of key possession:* 1.5 ms/key
    - *Generate vote:*
	    - *Persistent:* 135 µs/vote
	    - *Non-persistent:* 280 µs/vote
    - *Verify vote:*
	    - *Persistent:* 670 µs/vote
	    - *Non-persistent:* 1.4 ms/vote
- Certificate (for a realistic number of pools, stake distribution, and committee size)
    - *Generate certificate:* 90 ms/cert
    - *Verify certificate:* 130 ms/cert
    - *Determine weight (i.e., total stake voted for) in certificate:* 5.9 ms/cert
- Serialization
	- *Key registration:* 1.1 µs
	- *Vote:* 630 ns
	- *Certificate:* 65 µs 
- Deserialization
	- *Key registration:* 52 µs
	- *Vote:* 19 µs
	- *Certificate:* 2.7 ms

As a general rule of thumb, assume that 80% of votes are persistent and 20% are non-persistent. Here are details for how certificate operations vary with committee size, given a realistic stake distribution similar to that on Cardano mainnet.

| Number of pools | Number of committee seats | Generate certificate | Verify certificate | Weigh certificate |
|----------------:|--------------------------:|---------------------:|-------------------:|------------------:|
|            2500 |                       500 |              63.4 ms |           104.8 ms |           10.6 ms |
|            2500 |                       600 |              71.1 ms |           116.9 ms |           12.0 ms |
|            2500 |                       700 |              77.4 ms |           125.5 ms |           12.3 ms |
|            2500 |                       800 |              83.5 ms |           134.4 ms |           12.8 ms |
|            2500 |                       900 |              88.2 ms |           141.1 ms |           12.4 ms |
|            2500 |                      1000 |              92.5 ms |           144.9 ms |           12.3 ms |

[^3]: "Benchmarks and CLI for BLS cryptography used by Leios", https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/ReadMe.md

### Certificate size for realistic stake distributions

The following plots show number of persistent votes and votes, along with certificate size, for the `mainnet` stake distribution of Epoch 535. The dashed line in the first plot has slope one, so the gap between it and the solid line indicates the number of non-persistent voters. The certificate-size plot does not take into account a potential reduction in certificate size from omitting votes in excess of a quorum.

| Persistent voters                                        | Certificate size                                                 |
| -------------------------------------------------------- | ---------------------------------------------------------------- |
| ![Fait-accompli voters](images/fait-accompli-voters.svg) | ![Fait-accompli certificate size](images/fait-accompli-cert.svg) |

## Copyright

> [!NOTE]
> 
> The CIP must be explicitly licensed under acceptable copyright terms (see below).
> 
> CIPs are licensed in the public domain. More so, they must be licensed under one of the following licenses. Each new CIP must identify at least one acceptable license in its preamble. In addition, each license must be referenced by its respective abbreviation below in the _"Copyright"_ section.

This CIP is licensed under [Apache-2.0](http://www.apache.org/licenses/LICENSE-2.0).