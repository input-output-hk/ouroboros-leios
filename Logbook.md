# Leios logbook

## 2024-10-30

### Monthly demonstration and review

The first Leios monthly demonstration and review was held today, with approximately thirty attendees.

- [video recording](https://drive.google.com/file/d/12VE0__S0knHqXXpIVdXGWvDipK0g89p_/view?usp=sharing)
- [chat transscript](https://drive.google.com/file/d/1gqquDcsa6ESWH2KDfsEt39j2M5CvwThD/view?usp=sharing)
- [slides](https://docs.google.com/presentation/d/1KgjJyP6yZyZKCGum3deoIyooYUOretA9W6dTtXv1fso/edit?usp=sharing)
 
The following questions where raised and answered:

- **Q:** Will all pipeline stages be the same length? or will the implementation determine that?
	- **A:** It is currently envisioned that they will be the same length, but the exploratory modeling and prototyping can assess whether that this optimal.
- **Q:** Will IBs and EBs be stored forever after the chain has sync'ed after their inclusion in RBs?
	- **A:** Just the EB/IBS reachable from the (immutable) Ranking Blocks.
	- **A:** Some use cases will likely require examination of all IBs and EBs, so they need to be retained forever.
	- **A:** However, Mithril snapshots (or equivalent) might be sufficient for many use cases.
- **Q:** Do IB's contain unique TX?
	- **A:** Different IBs may contain the same tx. We are working on a sharding proposal at the moment. Hopefully we will get to discuss it in the next demo.
	- **Q:** So this is a DDoS vector?
	- **A:** Yes if it is not handled properly for the DDoS. Assuming you generate your view based on the settled certificates I do not see a possibility for split views. If you want to speculate on the IB ordering, then yes  care must be taken regarding split views.
- **Q**: Regarding non availability of IB, what is the effect on pipeline?
	- **A:** If an IB is not available, then no certificate will be generated for the EBs referencing it.
- **Q:** What about the selection processes? (How is permission to create or endorse being handled? Is it Praos 'like'?)
	- **A:** IBs, EBs,votes are created based on the VRF mechanism used in Praos.
- **Q:** The final certificates are being done on a Praos schedule? (I.e the certificate producer is selected the same way?) Hence has it same service interval distribution that we have at present?
	- **A:** Regarding the certificate rate, we are still working on realistic parameters, so I think we do not have an answer on this yet.
- **Q:** Regarding IB/EB lifetime, what happens if they don't diffuse within their assigned pipleline interval?
	- **A:** There is an inclusion horizon, so there is also a lifetime yes. Hopefully, we can take advantage of what we see in the network and drop them as early as possible.
- **Q:** This leads to 'how is an end user going to know if their tx has not been included' (so they can resubmit)?
	- **A:** Regarding non-inclusion, the simplest example is that the user sees that his tx is on an IB that is not in any of the certified EBs of the respective pipeline. Then he can deduce that his tx is not going to be included by this IB in the ledger.

Prompted by the discussion, there will be a separate, follow-up meeting to review delta-Q modeling:
	- Network saturation (phase change)
	- Modeling the node dynamically

Finally, there was general agreement that we need specific, quantitative input from stakeholders (projects, SPOs, etc.) regarding throughput requirements, including operating costs.

### ALBA voting

The Jupyter notebook [analysis/stake_distribution.ipynb](analysis/stake_distribution.ipynb) (view [here](https://nbviewer.org/github/input-output-hk/ouroboros-leios/blob/stake-analysis/analysis/stake_distribution.ipynb)) analyzes the implications of the Cardano mainnet stake distribution upon the number of unique votes and votes for a Leios voting round.

Leios needs to ensure the impossibility of an adversarial quorum, but it can accept adversarial activity causing quorum failures, since the latter just lowers throughput slightly. Hence we require a 60% quorum and 92% availability of honest votes, and set the committee size to 500 votes. An ALBA security parameter of 80 may provide adequate security. This translates to the following ALBA parameters and security for Leios.

- $n_f = 0.60$
- $n_p = 0.92$
- $l_\text{sec} = 80$
- $n_\text{votes} = 500$
- $2^{-l_\text{sec}} = 8.27 \cdot 10^{-25}$
- $u_\text{ALBA} = 148$
- probability of adversarial quorum
	- 35% adversarial stake: $p = 1.71 \cdot 10^{-21}$
	- 40% adversarial stake: $p = 7.69 \cdot 10^{-13}$
	- 45% adversarial stake: $p = 2.87 \cdot 10^{-7}$
- probability of honest quorum
	- 35% adversarial stake: $p = 0.917$

The plot below shows the number of votes that would have to be included in an ALBA certificate for Leios, given those parameters. If votes are 700 bytes each, then we have the following:

- Incoming to node which creates a certificate: 500 votes of 700 bytes = 350 kB.
- Contents of ALBA certificate: 140 votes of 700 bytes = 98 kB.

The alternative is to use BLS certificates, which have higher CPU load but smaller size.

![Number of unique votes in ALBA certificate for Leios](analysis/unique-votes-leios.png)

## 2024-10-29

### Team meeting

Agenda:

* Introduce William Wolff
* Short demo by Roland on newest ΔQ stuff
* Ledger preliminary design from giorgos

* Presentation by Roland of ΔQ modelling
  * comparing with Simon's Rust simulation, even if it does not simulate fully Leios
  * model the same things, ΔQ provide a high level comparable to Rust's simulation
  * Articulate how what ΔQ tool coordinates
* Ledger design presentation by Giorgos
  * how to avoid duplicates? => sharding, assign each tx and IB to shards => ensure tx are included in a single block
  * naive approach: use modulus, easy attack = add a nonce to a tx to be able to include it multiple IBs
  * => all txs are double spending, but fees get only paid once
* proposal:
  * fees paying token / shard, can freely be converted w/ ADA
  * IB of shard i should not have tx consuming token of shard j
  * fees of IB i are paid with token shard i
  * ensure IB from different shards will never consume token from other shards
  * *important* : fees are always paid, even if tx is not included in the ledger
  * Q: what about multiple tokens per UTxO?
  * grinding with people trying to overload one shard?
  * \# shards w.r.t IB rate => decrease probability of concurrent IBs for the same shard
* challenges:
  * a tx could be discarded but its fees would still be paid
  * pb in the case of apps which use "concurrent" state machine advance pattern -> perhaps this should not be free in the first place?
* assign shards in a "random" way, tune shards in such a way that transmission time makes the probability of the shards to overlap very low
  * needs to be grinding resistant
  * if shards are concurrent only x% of the time that may be acceptable
* multiple shard types on a single block to have more control over parallelism?
  * use VRF to generate a random sequence of "colors" to include in a block, attach colors to txs

### Rust simulation

Rewrote the simulation to use separate tokio tasks for each node, multithreading as much as possible. It can simulate 85tps in almost realtime, but the slowdown makes its results inaccurate (a smaller percentage of IBs propagated across the network compared to the non-netsim branch).

## 2024-10-28

### Rust simulation

In a branch (`non-netsim`), replaced the netsim library with a priority queue to see how fast the simulation's current architecture could run. It was able to simulate 85tps in realtime, but 850tps was too slow to be usable.

## 2024-10-25

### Rust simulation

The sim has been updated to support simple sharding between IBs, and to report on how long it takes a transaction to reach an IB.

## 2024-10-24

### Rough estimate of Leios resources

The spreatsheet [analysis/Leios resource estimates - ROUGH ESTIMATE.ods](analysis/Leios%20resource%20estimates%20-%20ROUGH%20ESTIMATE.ods) contains an initial rough estimate of the network and CPU resources required by Leios at three different throughputs:

- ~1,000 tx/s
- ~10,000 tx/s
- ~100,000 tx/s

Later work and simulations will refine this.

### Assessment criteria

Discussion #53 proposes assessment criteria for the continuation of Leios after PI8. The basic idea is to estimate bounds for the Leios curve in the following diagram. This is an attempt to view the economic and technical aspects of Leios's viability on the same chart.

![Leios Assessment Criteria for PI8](https://github.com/user-attachments/assets/e94287fe-0ad6-4805-98da-21cbbd134361)

The diagram above illustrates a techno-economic business case for Leios adoption that sheds light on the following questions.

1. What is the practical maximum throughput of Leios?
2. How far does that fall short of the theoretical maximum throughput?
3. How much would Leios transactions have to cost for SPOs to make a reasonable profit?
4. What is the worst-case bound for the throughput vs cost profile of Leios?
5. How does Leios compare to other blockchains?
6. Given current throughput targets, how much would Leios allow us to lower hardware requirements?
7. Given current hardware requirements, how much would Leios allow us to increase throughput?
8. What are the maximum limits Leios allows us to achieve at the maximum limits of currently available commodity hardware?

We could consider the following goals for January 2025.

- *Technical goal for PI8:* Estimate a reasonably tight upper bound on the cost of operating a Leios node, as a function of transaction throughput, and estimate the maximum practical throughput.
	- Target level: SRL2
- *Business goal for PI8:* Identify (a) the acceptable limit of transaction cost for Cardano stakeholders, (b) the maximum throughput required by stakeholders, and (c) the throughput-cost relationship for other major blockchains.
	- Target level: IRL3
- *Termination criteria for Leios:* Transaction costs are unacceptably high for Leios or the practical maximum throughput fails to meet stakeholder expectations. In this case the Leios protocol may need reconceptualization and redesign, or it may need to be abandoned.

### Haskell Simulation

* First batch of praos visualizations:
  - `cabal run viz praos-1` for a 2-node simulation relaying a chain
    across.
  - `cabal run viz praos-p2p-1` and `praos-p2p-2` for WIP simulations
    of ~100 nodes dynamically generating and diffusing blocks.

* CLI:
  - `cabal run viz` now lists the visualization names,
    as does `cabal run viz -- --help`.

* CI:
  - Haskell CI switched to use `haskell-actions/setup` instead of nix.
  - Isolated the formal spec nix setup by using a `dummy-project`
    instead of the repo root haskell project. Not a nix expert, others
    might find a better solution.

### Rust simulation

We experimented with a wasm build of the sim, it was difficult to get running because of ce-netsim using threads internally. The plan is to wait for changes to netsim before running the sim in browser. Next week, we are building a browser viz with "hard-coded" events (produced by the CLI version of the sim) so that we can get a head start.

## 2024-10-22

### NetSim

Discussion with NdP about the changes we would like to see in ce-netsim for the purpose of large-scale simulation of Leios, the main point being that we need the network simulator to also simulate time passing in order to avoid being dependent on the underlying computational power, ie. timestamps are attached by netsim's driver  to external events and passing of time is computed internally according to latency and bandwidth models

Next steps:

* NdP targeting version of netsim with simulated time by the end of November
* Short term: using a faster method to pop from the queue already makes it possible to run large scale simulation

### λείος Team Meeting

* Next week is Monthly demo & review
  * 1 slide with what's been promised
  * 1 slide with what's next
  * in between, a few slides or demos about what's been done
  * opportunity to ask deep questions, but there won't be time answer those => we can defer to another dedicated meeting to discuss important or lengthy questions
  * feedback received can change the project, it happened on Peras
  * it's more like a "bait" to trigger feedback from attendees and stakeholders
* what about mempool design?
  * there are other options
* Would be good to start with 2-3 slides description of Leios
  * Giorgos -> introduce high-level description of Leios
* Then about 30' of content
  * FM -> Andre?
  * ΔQ -> Roland
  * Haskell simulation -> Andrea
  * Rust simulation -> Simon
  * Ledger design?

* We want to define objectives for the next 2 months (eg. until end of December) by next Monday

* Next week's meeting
  * focus on sharding stuff, interesting the issue popped up also in the Rust simulation
  *
  * process question: need to know who is going to do the work?
    * let's write tickets for objectives
    * and then prioritise next meeting what we have

* focusing on short-leios would speedup things, so the main question for next 2 months can be reframed as:

  > How much resources would short Leios need and what would that imply in terms of cost for running a node?

  * We need to have an accurate description of Short Leios in a single place, copy/pasting from the paper with PNGs is just fine
  * Note: we've been bitten in Peras with having several, inconsistent documents floating around, and verbal descriptions

#### TODO

* [ ] Everyone: Define December objectives as GH issues
* [ ] Everyone: Fill in slides/placeholders & prepare for Wednesday demo meeting
* Next meeting:
  * Triage defined objectives according to priorities
  * GP to detail sharding ideas

### Rust simulation

The bug preventing IB propagation was caused by the netsim optimization; it removed delivery order guarantees. The sim has been updated to work correctly even if messages are received out-of-order, and now works enough to study IB delivery from its output.

When running with current transaction volume and 𝑓I = 5.0, IBs are extremely small and transactions are duplicated across many IBs.

 - 724 IB(s) were generated, on average 2.8171206225680936 per slot.
 - 234 out of 234 transaction(s) reached an IB.
 - Each transaction was included in an average of 4.653846153846154 IBs.
 - Each IB contained an average of 1.5041436464088398 transactions.
 - Each node received an average of 720.099 IBs.

We're going to try adding sharding to the simulation, to see if it lets us use network resources more efficiently.

At Pi's advice, we plan to take some time over the next week to visualize the parts of the sim that are implemented so far. We don't expect to use this for next week's demo, just making sure that the infrastructure is in place.

## 2024-10-21

### Rust simulation

We identified that the sim's failure to propagate messages was caused by an issue in ce-netsim. Profiling revealed a small issue in `netsim`, and correcting that fixed transaction propagation. When the sim is run faster than realtime, transaction propagation is still too slow.

To reproduce the issue, go to the `sim-rs` directory and run the following command:
```sh
RUST_LOG="debug,sim_rs::events=error" cargo run --release -- ./test_data/realistic.toml output/simple.json --trace-node 0 -t 1
```
The `-t` flag controls the simulation speed. `-t 1` means to run the sim at 1x real speed (1 slot per second). At `-t 1`, the logs will indicate that transactions propagate about as quickly as they are received. At `-t 16`, transactions are generated faster than they propagate.

We profiled netsim by using the rust [flamegraph](https://github.com/flamegraph-rs/flamegraph) crate with the below command:
```sh
cargo flamegraph -- ./test_data/realistic.toml output/simple.json --trace-node 0 -t 1
```
This generated a (very pretty) flamegraph showing CPU usage of the simulation. 92% of CPU time was spent inside of a call to `VecDeque::pop` inside of netsim: replacing that call with `VecDeque::swap_remove_back` dramatically improved performance.

Input blocks are failing to propagate due to what looks like a separate issue; some IBs propagate across the network immediately, other IBs never reach some nodes. This is likely a bug in the sim.

## 2024-10-17

### Rust simulation

The sim output is incorrect, apparently because IBs and TXs are propagating slowly. On a sim with 3000 nodes (2000 of which are stake pools) running for 1996 slots with 𝑓I = 5.0,
 - 8733 IB(s) were generated, on average 4.373059589384076 per slot.
 - 1187 out of 1647 transaction(s) reached an IB.
 - Each transaction was included in an average of 44.4936247723133 IBs.
 - Each IB contained an average of 8.391274476125043 transactions.
 - Each node received an average of 113.649 IBs.

## 2024-10-16

### Rust simulation

* First pass at input block body propagation
* Brief slack chat about mempool validation. It will be more complicated in Leios than in Praos; transactions can either come from IBs (which may or may not reach the final chain in some order) or from RBs (which are on the final chain). We don't need to worry about that for the sim yet, but it will be relevant for modeling CPU costs.

## 2024-10-15

### ΔQ Next steps

Discussing ΔQSD progress (and plans for next months)

* Roland currently focused on figuring out rules for expressing load, where the outcome is a CDF of some resources value over a (possibly infinite?) period of time
* Main question is: is the language suitable to model load?
  * Yves remarks we could just model thiings using probability directly without the intermediate language and that's been his thought reading the paper
* interim conclusion: language is useful, same expression can be evaluated in the timeliness or load context?
  * is the result relevant?
* what we are interested in is the distribution of bandwidth consumption for one node we should shift our focus from a global property (delay across the network) to a local one (resources consumption for a single node), ie. reason about a node, parameterised by say its connectivity?
  * Then given some assumptions about the node's location, we could also model the cost of running Leios
* Tricky part is modelling the "recursion" or "exponentiation" of some outcome expression given possible number of repetitions
  * global clustering coefficient

* Next steps (1w):
  * Roland try to fit CDF of throughput in ΔQ
  * Yves try to go down the probability route with a notebook
  * We compare notes next week
  * see [#41](https://github.com/input-output-hk/ouroboros-leios/issues/41)

## 2024-10-15

### AB - Conformance testing exploration

Investigating how https://github.com/stevana/coverage-guided-pbt/ could be used to explore traces in Leios, in the context of state-machine based tests

* Ensure the implementation generates logs on top of results => combined "language" that can be used in coverage assertions
* Define some combinators that checks some logs have been covered,  possibly using a predicate?
* Generate traces, guided by coverage metrics

Got side-tracked into dependency hell and different versions of GHC:

* The coverage-guided-pbt repo has a lower bound dependency on `base >= 4.20` which means it requires ghc 9.10
* Then tried to configure Emacs to use eglot LSP client instead of lsp-mode. Found out a way to configure the workspace to use `stylish-haskell` formatter using `.dir-locals.el` config, but it seems not to be called...
* Trying to install stylish-haskell globally with `cabal install stylish-haskell` -> does not work with ghc 9.10.1 (!) and HLS for 9.10.1 does not support it as a plugin
* Tried to enter nix shell on remote machine, but it fails with a cryptic error
* I switched to base 4.19 and GHC 9.8.2 then stylish-haskell plugin is available, and the code is formatted. Also, reverted to use `lsp-mode` as `eglot` does not provide any code actions

Main question is what to test (first)? And how to test? Network diffusion seems like a good candidate, with the SUT representing a single node and the test focusing on the timeliness and correctness of the diffusion process:

* The node can fetch new headers and blocks
* The node can diffuse new headers and blocks
* It must node propagate equivocated blocks more than once
  * But it must propagate them at least once to ensure a _proof-of-equivocation_ is available to all honest nodes in the network

How does coverage comes into play here?

* The node emits logs, which we know the language of
  * node receives a header
  * node receives a body
  * node diffuse a header
  * node diffuse a body
  * node sees an equivocated block
  * node blacklist a peer
* There's a correlation between messages we want to observe, ie:
  * see equivocated block ---> node blacklist a peer ?

### Team meeting

Meeting goal: define or refine objectives for remaining 2 months

* There's an admin side to this as part of internal PI planning cycle but it's less important than aligning on clear goals
* We know there will be "dev rel" role dedicated to Leios to connect w/ the community

We need to answer some questions asked from the demos yesterday:
* "Why are simulations not using Agda code?"
  * Q: what's the availability of andre knispel?
  * he will be dedicated to Leios and we also have Yves
* "Why a rust ΔQ tool when there exists other tools?"

Discussing some possible short-term objectives:
* On conformance testing
  * define interface b/w testers and implementations
  * start with Adversarial scenarios, answering the question on where to define the behaviour: in the spec or in the tester?
  * simulatios/prototypes will need to have some ways to interact w/ tester => interfaces can be refined later
* Define a taxonomy of "adversarialness"
  * strong adversary that's _misbehaving_
  * adversarial "natural" conditions, eg. outages/split brains
  * transaction level adversary
  * we need to qualify those different scenarios
* throughput bounds/measurements
  * "will the leios node be so expensive community won't like it?"
  * we want to provide a model, map the possible tradeoffs and the relationship b/w different resources and functionalities provided by Leios
  * It's important to learn from the mistakes from hydra, esp. w.r.t communication: avoid discrepancy b/w narrative and reality leading to FUD
  * the previous CIP from 2022 had some numbers, ie. ~1000 tps based on network traffic pattern simulation
  * based on assumptions about the design: each link b/w peer is 1Mb/s (50 Mb/s for ~20 nodes)
  * current solana throughput is ~65k tps
* we do not need lot of simulation to answer those questions
  * network bandwidth not a limiting factor, above assumptions are an order of magnitude from saturating the network
  * CPU will be a limiting factor: if 1 IB takes 100 ms to validate, then this means one can validate 10 IB/s
* we also need to compute costof resources
  * for various scenarios -> 1k / 10k / 100k tps
  * when saturating a network from high end data center
  * keep a stream of approximate calculations alive, and iterate

* some speculation: Leios fees might be cheaper than Praos, because there's more competition for resources on Praos?
  * in general, it could be the case we price tx differently
* Mempool design -> sharding?
  * depends on resources pressure on CPU
  * existing nodes already have 4 cores

Objectives:  We should give ourselves until end of next week to write down and refine 3-4 concrete objectives for the next 2 months

**Conformance**
* Write an Agda executable spec
* Establish a conformance pipeline from Agda spec to prototypes
* Test relevant adversarial scenarios (equivocated blocks and votes, possibly DoS attempts, split-brains, network outages and delays...)

**Data collection & load modelling**
* Provide answers to resources questions -> Revive results from earlier CIP
* We need data on validation time -> relationship b/w block size/exec budget -> waht's the time budget
* Build an integrated spreadsheet to explore the "resources space"
* Communicate resources model to the community

### Rust simulation

* First pass at input block generation and header propagation
* PR open with the above

## 2024-10-14

### Discussing Conformance testing approach

We are trying to understand the link between formal ledger specification and cardano-ledger, as we want to find a better way to relate Agda spec w/ actual code building a conformance testing suite:

* Formal specification lives in [formal-ledger-specifications](https://github.com/IntersectMBO/formal-ledger-specifications) repository
  * There is a branch there called `MAlonzo-code` which contains MAlonzo-based generated Haskell code from the spec
* This branch is referred to in the [cabal.project](https://github.com/IntersectMBO/cardano-ledger/blob/master/cabal.project#L21) of cardano-ledger as a source-level dependency
* The toplevle module in the generated code is name `Lib`
  * Perhaps a [more descriptive name](https://github.com/IntersectMBO/formal-ledger-specifications/issues/595) would be useful?
* This module is imported and renamed as `Agda` in cardano-ledger repo, in the `cardano-ledger-conformance` library

The link between the formal spec and the ledger impl is mediated by the [constrained-generators](https://github.com/IntersectMBO/cardano-ledger/tree/master/libs/constrained-generators) library which provides a DSL for expressing constraintss from which generators, shrinkers, and predicate can be derived:

* Traces tests use `minitraceEither` is a generator for traces in the Small-step semantics of the ledger
* the `ExecSpecRule` typeclass is defined for the various categories of transactions (eg. `POOL`, `RATIFY`, etc.) and provides methods for producing constrained spec expressions
* the `runAgdaRule` methods does the linking between an environment, a state and a transition, "executing" the corresponding Agda rule
* the `checkConformance` function ultimately calls the latter and does the comparison

We can run the conformance tests in the ledger spec :tada:

#### What approach for Leios?

* We don't have an executable Agda spec for Leios, only a relational one (with holes).
* We need to make the spec executable, but we know from experience with Peras that maintaining _both_ a  relational spec and an executable spec is costly
  * to guarantee at least soundness we need to prove the executable spec implements correctly the relational one which is non trivial
* Also, a larger question is how do we handle adversarial behaviour in the spec?
  * it's expected the specification uses dependent types to express the preconditions for a transition, so that only valid transitions can be expressed at the level of the specification
  * but we want the _implementaiton_ to also rule out those transitions and therefore we want to explicitly test failed preconditions
* then the question is: how does the (executable) specification handles failed preconditions? does it crash? can we know in some ways it failed?
  * we need to figure how this is done in the ledger spec
* In the case of Peras, we started out modelling an `Adversary` or dishonest node in the spec but this proved cumbersome and we needed to relax or remove that constraint to make progress
  * however, it seems we really want the executable spec to be _total_ in the sense that any sequence of transitions, valid or invalid, has a definite result

* we have summarized short term plan [here](https://github.com/input-output-hk/ouroboros-leios/issues/42)
* we also need to define a "longer" term plan, eg. 2 months horizon

## 2024-10-10

### Approximate transaction sizes and frequencies

Using post-Byron `mainnet` data from `cardano-db-sync`, we tally the transaction sizes and number of transactions per block.

```sql
-- Transaction sizes.
select size
  from tx
  where size > 0
    and block_id >= 5000000
    and valid_contract
;

-- Number of transactions per block.
select count(*)
  from tx
  where block_id >= 5000000
    and valid_contract
  group by block_id
;
```

As a rough approximation, we can model the size distribution by a log-normal distribution with log-mean of `6.833` and log-standard-deviation of `1.127` and the transactions per block as an exponential distribution with mean `16.97`. The plots below compare the empirical distributions to these approximations.

| Transaction Size                                     | Transactions per Block                                    |
| ---------------------------------------------------- | --------------------------------------------------------- |
| ![Transaction size distribution](images/tx-size.svg) | ![Transaction-per-block distribution](images/tx-freq.svg) |

The transaction-size distribution has a longer tail and more clumpiness than the log-normal approximation, but the transaction-per-block distribution is consistent with an exponential distribution. Note, however, that there is a correlation between size and number per block, so we'd really need to model the joint distribution. For the time being, these two approximation should be adequate.

See the notebook [analysis/tx.ipynb](analysis/tx.ipynb) for details of the analysis.

### Open tasks for research

* Transition from a split-bandwidth description of the network for Leios (each type of message is allocated some part of the bandwidth) to a uniform priority based download policy.
* How to avoid conflicts, duplicates, and fees not being paid at the ledger level? Is avoiding conflicts the responsibility of the user or of the system?
* What applications are supported by a Blob-Leios version where certificates do not end up on-chain?

## 2024-10-04

### Retiring leios-sim

* Delete `leios-sim` haskell project
* Delete CI steps to deploy the simulation server
* Remove link to the simulation from site main page

### ΔQ Modelling experiment

* we (Roland, Yves, Arnaud) start with basic network and latency model from the "Mind your outcomes" paper
* assume a 1MB IB, just to get a sense of how far we can push this
* It takes about 6s for such a block to reaech > 99% of nodes
  * using same assumptions for network topology than
* adding 3s delay for validation
* diffusion of EB ~ 2.9s

* Q: How long does a tx/block validation takes?
  * need to get more data about this
  * this must obviously be lower than L as that's the duration of the `Link` phase
  * This leads us to a discussion on tx duplication/validation/inclusion which we won't tackle

* Rough preliminary conclusion is that λL should be around 6s with those parameters to ensure IBs get diffused across the network in a timely way
  * fun fact: these are the default parameters in leios-sim

* Given the way Leios works, it's not clear that modelling a "loaded system" would be interesting: Everything is "clocked" by the rounds (L) and as nodes are pulling data, the only thing that can happen is that IBs are more or less full.
  * Load would have an impact if we model at the level of transactions, because that's the thing the protocol has no control over.
  * Or could it be the case that we want to model what happens at saturation of the network capacity? => seems like in practice, the limits are quite high.

* Possible next steps: build a network model on time-to-chain for individual txs under load

### Rust simulation

- Sim is modeling transactions as an id and a size in bytes.
  - The model was chosen ad-hoc to "look good", unlikely to reflect reality.
- Next step is to model block diffusion, hopefully converging on network design with the haskell simulation of Praos

## 2024-10-03

### Team discussion

- leios-sim
    - More about the protocol than the network
    - Input blocks are generated and endorsement blocks are generated referencing them
    - No voting in the simulation
    - We really don't need this now, given the network-orientic approach we are adopting
    - Probably delete it eventually
    - Delete this folder and record it in the log book
- Use permalinks and commit hashes in logbook entries
- Shared formats
    - Do this incrementally
    - We generally intend not to have duplicate formats
    - The first workstream to create a format will have it reviewed by other workstreams
    - A common output format might be more important the input format
- Arnaud will ask for data
    - CF for data on load and topology
    - Blockfrost for additional data
- Leios might need some sort of sharding or detection for mempool difussion
    - Mempool diffusion modeling will eventually be needed
    - Do this later
- Monthly demo & review meetings
    - Last week of the month
- Switch to one team meeting per week
- Next step on DeltaQ is to reproduce the timeliness analysis
    - Will add import/export functionality

### Rust simulation

- Sim runs a slot lottery and decides which pool(s) produce block(s)
- Sim reads input (protocol parameters and pools) from a toml file
- Sim writes output (list of events and timestamps) to a json file
- Next steps:
    - Create (extremely basic) fake transactions to measure throughput

## 2024-10-02

### Team discussion of Haskell simulation

- What general approach are we planning to take?
    - What questions?
    - What level of detail?
    - What order to do things?
- What we don't need to model (at least initially)
    - The content of the ledger
        - Not needed for most questions
        - Can be done later
        - Instead, just model input block in terms of size
        - Cannot answer questions about tx lifecycle
    - Shared formats not needed for now
- Approach
    - Start with existing network simulation, which is just a traffic simulation
    - Go back an do praos
        - 100s of nodes
        - Visualization
    - Add leios
        - Depart from paper by accounting for asynchrony in implementation
        - Might write an asynchronous version of the leios specification
        - Haskell stm version could be very similar to asynchronous leios spec
    - Stick with gtk visualizations
        - Record videos for dissemination
- Questions that can be answered
    - Praos questions
        - Validate
    - Leios
        - Time for IB to RB
        - Repeat measurements for leios
- Other
    - Rust might be the better option for visualization
    - Outputs from both simulations might both be visualizable with the same tool
- For Thursday
    - [ ] Visualizaiton approach
    - [ ] Are common formats really not needed?
    - [ ] What is the status of the [leios-sim/](leios-simm/) folder?
    - [ ] What questions do we lose by having no simulation of txs?

### Leios & Delta-Q

ND starts raising a few concerns he has about leios that should be answered:

* How much will settlement change?
* What's happening at high loads?
* How does it work at saturation?

A key issue is potential attack vector that comes from de-duplicating txs: how is it handled by Leios forwarding infra? In general, how does Leios deals with adversarial behaviour?
We acknowledge this needs to be answered, and there's work on mempool management that needs to happen, but that's not the core topic we want to work on _now_

Another important question to answer is "What resources are needed?" as this has a deep impact on centralisation:
* people come to Cardano because they can run a node cheaply
* Leios might excludes most of the user base

RK => how does hardware requirements change? how ΔQ can express these?

Shelley implements isometric flow control system
* receiver has control over the load it handles
* blocking occurs at the point of congestion

The system changes at the point of blocking -> need to allow the blocking to go away, waves of phase change goes across the system
* ~ backpressure
* it's a strong requirement to make it as lossless as possible

Removing duplicates is a necessity for long term efficiency of the system, might have an impact on the system
* we are not solving it right now but need to ensure this question is investigated down the road

Key metrics:
* how long to reach the block?
* how much computational power?
* how much data flow?
* how much storage does Leios requires?

2 models:
* average case
* heavy load

another model:
* cost impact of Leios, cost of networking/storage -> updating fee model

* Talk to Karl about network topology

Making it worthwhile to have distributed nodes? -> resolving height battles

Socializing results and constraints, trygin to get actual numbers from product/usage

## 2024-10-01

Report on ΔQ work in Rust so far (Roland):

- implemented MVP in the sense of being able to create ΔQ expressions as per the “Mind your outcomes” paper and evaluate them
- added a recursion operator that is purely syntactical: recursive unfolding of a named expression with a given depth limit
- project uses yew/trunk to render the HTML/CSS frontend, which uses WASM (tools were chosen for convenience, not minimalism)
- ΔQ evaluation currently done in server process, but could also be moved into the web part (should use web worker to stay responsive)

Implementation notes:

- CDF is represented as a list of f32 tuples, with a size limit of 1000 (tunable) after which the step function will be simplified (i.e. approximated)
- this simplification can be done in over- or under-approximation mode; running both and showing the difference will illustrate the error range
- tuples are pruned in increasing order of their distance to the right neighbour, with two complications:
  1. distances are binned to some precision to avoid dominating the selection by floating-point precision limits
  2. the algorithm pulls pruning candidates from a heap but skips every second one of the same distance; this yields more even pruning along the x axis
- the EvaluationContext holds all named expressions and allows resolving names, but also tracks the current recursion allowance for each name
  (recursion with allowance isn’t allowed while already recursing on that name; allowing this results in infinite loop)

Comments raised while presenting this to the team today:

- syntax should stay closer to the original paper (I deviated in order to allow normal people to type in expressions with their keyboard)
  - this could be done by having aliases and supporting the entry of special glyphs with a palette on the web page
- showing recursion as exponentiation is surprising, Andre expected exponentiation to be just some form of repeated multiplication (but unclear which operation that would be)
- recursion as template unfolding was understood as some fix point representation by Duncan, but currently that is not how it is implemented
- treating the propagation of messages across a network graph isn’t faithfully modelled, but it could be if recursion was actually some kind of fix point operation
  - it would be great to have an operator that expresses “only broadcast the first copy of the message I receive”, which would allow pruning the infinite evaluation tree
  - this is unclear to me because ΔQ speaks in CDFs which aren’t concrete in this way, so pruning wouldn’t apply to CDFs but to some execution of the modelled process
- Pi asked how this work relates to the Rust-based network graph simulator, which has at least two answers:
  - compute CDFs that are used by the simulator using ΔQ
  - use simulation results (CDFs) as inputs for further ΔQ modelling, e.g. on a higher level
- on the website we’ll need something that can quickly answer high-level questions, running a simulation would probably not be feasible but ΔQ should be
- it occurred to me that if we can get a load profile from a ΔQ model, we can then use queueing theory to compute the effect on latencies to get a better approximation of overall system behaviour
  - these two steps can be run alternatingly to see if there is a fix point for the result — and if the computation diverges, that tells us that the network graph would die from overload

## 2024-09-30

Catching-up on Leios ΔQ work:

* pulled updated main and trying to run it. It uses [trunk](https://trunkrs.dev) which is a tool for packaging WASM app that takes care of all the dependencies and nitty-gritty details of Rust -> Wasm toolchain.
  `trunk` build does not automatically instead needed toolchain actually, so one needs to add the toolchain and (on Mac M1) install manually wasm bindings generators.
* actually takes quite a while to compile!!
* added some documentation to the README to remove a couple hurdles from installation process. I guess nix does "the right thing"?
* It seems like [wasmpack](https://github.com/rustwasm/book/issues/160) should do it, so perhaps we could use wasm-pack rather than `trunk`? Or does this even make sense?

Trying to get a high-level view of the Leios project:

* WT (Duncan, Andrea, Wen) -> working on network simulation?
  * there's an old code base in `simulation` directory which contains a simulator for "simple" packets routing?
  * What kind of question can it answers in relationship with Leios?
* Sundae (Simon)
  * network simulation?
  * ledger? how does this relate to other group working on ledger?
  * why care about ledger? could we not model IBs more abstractly?
* Roland / Yves?
  * ΔQ modelling tool
  * ΔQ modelling of Leios proper (start with short pipeline Leios?)
  * exploring use of ΔQ for modeling load and congestion?
* Brian
  * filling up AB's role
* Andre Knispel
  * protocol specification in Agda
  * leios ledger spec?
* Giorgos
  * research liaison -> ledger design?

Possible list of short-term goals:

* Update protocol simulation (using Agda as an executable spec?)
* ΔQ modelling of timeliness (and load/congestion ?)
* Large scale network simulation (using ce-netsim ?)
* Leios requirements for Ledger (adjust Praos design? simulate impact of Leios on ledger?)
* Existing network simulation from 2 years ago?

During a discussion about Leios and FM, Briand suggested we write a white paper on Agda-based conformance testing:

* testing strategies for consensus, ledger, or plutus are different
* Is Agda2hs is fit for purpose? Seems like there's some dissent within the Agda experts about this
* At the very least, writing things down will "force" dialogue and help reach consensus/alignment on a particular way of working

## 2024-09-26

### Team session on requirements for metrics

- Reviewed status of certificates
	- Options
		- ALBA
		- BLS
		- other
	- Dimitar, Raphael, Tolik, and Pyrrhos are investigating viability of ALBA
		- Potential use of ZK to reduce size
		- Non-ALBA options are still on the table
- Reviewed plan for Sundae Labs work
	- First step is a simplified Praos ledger
		- Transactions remove UTxOs and add new UTxOs
		- Transactions are opaque objects with an identifier (hash) and padding/representation of size in bytes
		- Delays caused by cryptography etc. are modeled
		- Ledger is set of active inputs
	- Subsequent steps
		- IBs
		- EBs
		- Votes 1
		- Endorsement
		- Votes 2
		- L1 diffusion
		- . . .
- Brainstorming of metrics, experiments, variants, etc.
	- Generate loads randomly and/or based on historical data.
		- DB sync provides distributions of transaction sizes, etc.
		- Mempool data requires more effort to extract
	- Experiment with measuring throughput at 20%, 40%, 60%, 80% of theoretical network bandwidth.
	- Measure memory and disk growth.
	- Can services be run as separate components, on separate VMs, with varied levels of trust, with/without large amount of stake?
	- Packing of transactions:
		- Measure % duplicate, % conflicting, % non-conflicting txs in final ledger update
		- Scoopers and other Dex batching may naturally produce conflicting txs
	- Design an attack scenario that maximizes conflicts and/or duplicates.
	- Memory pool modeling may be necessary:
		- Investigate what logic will be used to include txs in IBs.
		- If a node is elected twice in short succession, can it include dependencies of the second IB upon the first?
	- Consider design variant where input blocks (minus VRF signature) are proposed and then adopted (adding signature).
	- What is the latency distribution of nodes receive txs/IBs after they are referenced by the ranking block?
		- How long does it take txs to reach the slowest nodes?
	- What is the optimal IB size?
	- Could third parties propose an IB that is then signed by a VRF-elected Leios node?
	- Can IBs depend upon IBs?
		- Will Leios adversely affect tx batching and chaining?
	- Compare freshest first vs oldest first.
	- Are there synergies or conflicts with Validation Zones (Babbel Fees)?
		- Are the validation zones the same as IBs?
		- Are the tx-reconciliation algorithms for validation zones and IBs compatible?
	- Might adding more Leios stages improve throughput?
	- Is this level of node/ledger change impractical for the ecosystem?
		- Should Leios be more like a high-throughput side chain (L1.5)?
	- Assess the API impact of Leios for node following, indexing, etc.
- Next week settle on initial common formats for simulation I/O.
	- Protocol parameters
	- Crypto: CPU delays and signature/certificate sizes
	- Network nodes and topology
	- Output traces
- Use Haskell's Aeson-style YAML serialization and configure Serde to mimic that in Rust.

## 2024-09-25

### Team session on network simulation

- Plans to evaluate [leios-sim](leios-sim/)
    - How faithful is it to the Agda spec?
    - Will major refactoring be needed?
    - Is it engineered well enough to warrant extending?
- Discussed the need for property-testing generators that have good coverage.
    - Both "spatial" and "temporal" constraints exist
    - Ideas
        - Lazy search
        - SMT solver
        - . . .
    - Ledger has had some success
    - Packages
        - [Plutus approach](https://github.com/IntersectMBO/plutus/tree/master/plutus-core/testlib/PlutusCore/Generators/NEAT): Agda + Haskell
        - [Constrained generators](https://github.com/IntersectMBO/cardano-ledger/tree/master/libs%2Fconstrained-generators): Haskell
- Rust simulation work is progressing
    - Use of CE-Netsim seems straightforward
    - Full-time work may start next week, depending upon final signatures to the contract
- Clarifications
    - The `L` parameter is some multiple of the slot length, probably dozens of slots
    - Is header diffusion a push or pull process?
	    - The Leios paper differs from Cardano practice.
	    - The two approaches may be isomorphic.
    - The paper has some ambiguity regarding whether handling equivocations is strictly part of simplified or full Leios
    - IBs might be diffused to neighbors if they nominally valid but the node might nevertheless choose not to vote on them
- A few concerns about Leios that may need early investigation
    - Will some pipeline segments become clogged and starve other segments, resulting in much lower throughput than theoretically possible?
    - What are realistic bounds on throughput?
        - This would provide concrete information about what to expect and might ground the Leios discussions that are occurring in the community.
    - How much will ledger-level operations impact Leios, perhaps throttling its throughput?

## 2024-09-20

### Team meeting

- Introductions and roles
    - Excellent balance of Agda, Haskell, and Rust skills
- Reviewed administrative informoration
    - PI7 Jira tickets, mirrored at [#16](https://github.com/input-output-hk/ouroboros-leios/issues/16), [#17](https://github.com/input-output-hk/ouroboros-leios/issues/17), [#18](https://github.com/input-output-hk/ouroboros-leios/issues/18)
    - Nominal objectives, tasks, and deliverables for next 12 months
- Work agreement
    - Write down “everything” in a “research journal”
        - what we do
        - why we do it
        - what are the expected results vs. actual results.
    - Regular (at least weekly) technical review of all work done by everyone
    - Show & tell sessions
    - Communicate with the stakeholders (including community) on a regular basis
    - Experimenting, pivoting, and dead-ends provide valuable learnings and should be documented in logbook
    - Processes and workflows can emerge from our needs, and do not have to match typical production enviroments
        - However, QA and checking each others' work is important
    - Ensure all results are “easily” reproducible by the community
    - Arnaud will pair with engineering staff each week in October
    - Technical report each quarter -- the next will be in December
    - CIP at conclusion of innovation workstream
- Project resources listed at [discussion #15](https://github.com/input-output-hk/ouroboros-leios/discussions/15)
- Open discussion
    - Leios flavors
        - Blob, short, simplified, and full
        - All flavors have the same security guarantees
        - Blob Leios does not deal with Cardano transactions
        - Full Leios adds robust throughput even in the face of performance issues in base protocol
    - Details of interaction with ledger
        - Fairness for fees
        - Wastage (i.e., duplicate or conflicting transactions)
        - Time-dependent smart contracts
    - Demo of initial DeltaQ rust implementation by Roland
    - Brian will coordinate with David about contracts and with Hans about tweeting
- Communication and collaboration
    - Use slack channel for admistrative and scheduling
    - Use github [discussions](https://github.com/input-output-hk/ouroboros-leios/discussions) or [pull requests](https://github.com/input-output-hk/ouroboros-leios/pulls)
        - When relevant, summarize discussion results or PR comments in [this logbook](./Logbook.md)
    - Put experimental code and work in progress on the main branch of [this repository](./)
        - Avoid long-lived branches
        - If warranted, code can later be separated into a new repository via `git subtree`
        - Mostly keep main branch passing the CI, but short-lived exceptions are okay
        - Describe new work and findings in [this logbook](./Logbook.md)
    - Approximately three working meetings per week
        - Each meeting (or slack) will settle the topic for the next meeting
- Next steps
    - Meetings next week approximately at 1400 UTC
        - Duncan will present on existing ouroboros network
        - Two meetings to discuss, brainstorm, and plan network simulations
    - Future meetings
        - Duncan will present on ouroboros consensus protocol
        - Duncan will present on praos lessons learned
        - Arnaud, Yves, or Brian will present on peras lessons learned
        - Andre will present on formalization lessons learned
        - Additional protocol and formalization meetings
        - At some point we'll meet with PNSol about DeltaQ collaboration
    - Possible in-person meeting mid December or January?
    - Work focus
        - Roland and Yves will collaborate on DeltaQ
        - Everyone should familiarize themselves with the [simulation/](simulation/) and [leios-sim/](leios-sim/) code
            - Live version of `leios-sim` at https://leios-simulation.cardano-scaling.org/index.html
            - Run `simulation` locally via [instructions below](#running-ouroborous-net-viz-in-the-browser)

## 2024-08-30

### Nix and CI support for Leios specification

The Nix flake now builds the Leios specification and the libraries upon which it depends. The type checking of the spec is now added to the CI.

```console
$ nix develop

Welcome to Ouroboros Leios!

Locations of Agda libraries:
  /nix/store/1yxiwwy44xxxgzdmvyjizq53w9cfinkn-standard-library-2.0/standard-library.agda-lib
  /nix/store/ppsczpm7l2gx1zd3cx2brv49069krzzh-agda-stdlib-classes-2.0/standard-library-classes.agda-lib
  /nix/store/gkci6kgv4v9qw2rh5gc0s26g53b253jy-agda-stdlib-meta-2.0/standard-library-meta.agda-lib
  /nix/store/2gk6rvsplxww4i8dnflxbd319lfxdcvv-formal-ledger-1d77a35a/formal-ledger.agda-lib

Run 'emacs' to edit .agda files.


Type 'info' to see what's inside this shell.

$ cd formal-spec

$ emacs Leios/SimpleSpec.agda
```

## 2024-07-26

### Running `ouroborous-net-viz` in the browser

It is relatively straightforward to run GTK applications like `ouroborous-net-viz` in a web browser. Here is one recipe.

Start a broadway daemon:

```console
$ nix develop

$ broadwayd --port 8282 :5
Listening on /run/user/120065/broadway6.socket
```

In another terminal window, run the visualizer using the broadway backend, ignoring the messages:

```console
$ GDK_BACKEND=broadway BROADWAY_DISPLAY=:5 nix run .#ouroboros-net-vis -- p2p-1
/nix/store/aw2fw9ag10wr9pf0qk4nk5sxi0q0bn56-glibc-2.37-8/lib/libc.so.6: version `GLIBC_2.38' not found (required by /nix/store/rgafsh9w6yrklqbmz6gb0cvdy10ja9mv-libxfce4util-4.18.2/lib/libxfce4util.so.7)
Failed to load module: /nix/store/s9ah4nlrxxbmzzzwqp3rf43cyr0cwnv7-xfconf-4.18.3/lib/gio/modules/libxfconfgsettingsbackend.so
/nix/store/aw2fw9ag10wr9pf0qk4nk5sxi0q0bn56-glibc-2.37-8/lib/libc.so.6: version `GLIBC_2.38' not found (required by /nix/store/nf5mmvq3cayv4z3jcnhapiqjzh3brcd2-gvfs-1.54.1/lib/gio/modules/libgvfsdbus.so)
Failed to load module: /nix/store/nf5mmvq3cayv4z3jcnhapiqjzh3brcd2-gvfs-1.54.1/lib/gio/modules/libgvfsdbus.so
```

Visit `localhost:8282` in the browser.

Here is a video: [![image](https://github.com/user-attachments/assets/88af2794-148a-49d8-8164-ba8790b6b3de)](https://vimeo.com/990683045/74a915afd2?share=copy)

We'd have to add session management and UI components to make this generally useful. Alternatively, it could be packaged as a Docker image.

### Dependency upgrades, Nix, and CI

- We upgraded [ouroboros-net-sim](./simulation/) to use the latest `io-sim`, `io-classes`, and `si-timers` with very few changes to the source code and with the addition of a new `TimeCompat` module.
- A nix shell and derivations was also added for the targets in the project.
- Builds and tests were added to the CI

## 2024-07-19

### Comments on `leios-sim`

Here are a few comments by @bwbush about the `leios-sim` package:

1. I think we should bite the bullet and add a `MonadRandom` instance to io-classes. Explicitly passing RNGs around makes the code harder to read and refactor.
2. Even without that, when the code becomes more complicated, we should consider using a monad transformer stack that includes a `MonadRandom` instance.
3. Along the same lines, we might want to minimize or hide the use of `TVars` and offload that to some State types so functions can live in `MonadState`. Once again, this will let the implementation functions read more abstractly and make later refactoring easier as the implementation evolves.
4. The unit conversion that we have to do (e.g., seconds to milliseconds) have always bothered me because it would be easy to make a mistake. Having put the unit in `bitsPerSecond` helps somewhat.
    1. Use one of the time types (or even `Data.Fixed`) instead of a custom `Microseconds` would help somewhat.
    2. The typechecked dimension packages like [units](https://hackage.haskell.org/package/units) feels like overkill, but maybe they are worth it. My understanding is that these dimensional analysis packages have no runtime overhead: they'd prevent unit errors at compile time.
5. The use of newtype wrappers was good. We could automatically derive Num instances for those, but that would decrease safety at the expense of increasing readability. (Hence, my comment on units.) I'm not sure.
6. I think the design does a reasonable job of separating the transport aspects from the logic aspects. We'll probably need a more sophisticated network representations, maybe event separating the network interface from the network itself.
    1. BTW, I think a big challenge for leios prototyping will be accurately representing network contention between the different leios roles, the base protocol, and the memory pool in high-throughput situations. Even without an adversary, I'm concerned that some parts of the implementation might starve others.
7. So far as I can tell, the simulation reasonably approximates a simplified Leios.
8. The complexity and verbosity are okay at this point because it's laying necessary groundwork (subject to refactoring) for the next level of fidelity: it highlights areas of complexity and opportunities for modularization. I think the Leios simulation will need many cycles of refactoring in order to control complexity and leverage modularity.

### Document simulation

Added some documentation to the Leios simulator:

* Added _tooltips_ to document the various parameters available
* Added readonly fields computing various aggregates from the simulation's data: Throughput, latency to inclusion in EB, dropped IB rate
* Added a [comment](https://github.com/input-output-hk/ouroboros-leios/issues/7#issuecomment-2236521300) on the simulator issue as I got perplexed with the throughput computation's result: I might be doing something wrong and not computing what I think I am computing as the results are inconsistent. I think this comes from the fact we are simulation 2 nodes so the throughput aggregates the 2 nodes' and should be assigned individually to each one, perhaps more as a distribution?

## 2024-07-11

### Deploying simulation in the "cloud"

Started working on simnulation deployment on AWS.
  * Found this repository for setting up ECS which sounds the most promising option: https://github.com/ajimbong/terraform-ecs-cicd-project.
  * This article contains the GHA workflow part: https://ajimbong.medium.com/deploy-a-docker-container-to-amazon-ecs-using-github-actions-fd50261b8e03
  * Following tutorial here: https://developer.hashicorp.com/terraform/tutorials/aws-get-started/aws-build
  * installing AWS command-line from https://docs.aws.amazon.com/cli/latest/userguide/getting-started-install.html

Created service account `leios-build` with power user rights, and generated access keys. TODO: reduce rights to the strict minimum

Managed to deploy ECS cluster with defined service, but there's no EC2 instance container attached so it cannot run :( => use Fargate?

Managed to configure the ECS cluster, service, and task to run the image, but it now fails to download the manifest from ghcr.io which seems a permissions issue. I need to add the necessary configuration to the task/service?

need to configure a secret containing a PAT for pulling the manifest: https://docs.aws.amazon.com/AmazonECS/latest/developerguide/task_definition_parameters.html#container_definition_repositoryCredentials

I gave up trying to run on AWS, every solution I found is an insanely intricate maze of stupidly complicated solution which I don't care about as I only need to deploy a _single_ image without any data dependency attached.

I managed to get Gcloud run deployment working, mostly copy pasting what I did peras and fiddling with it.

* I reused same service account than Peras which is  a mistake -> should create a new service account with limited rights
* Needeed to add service account as an _owner_ of the domain in the google console (a manual task) in order to allow subdomain mapping
* Changed the server code to support defining its port from `PORT` environment variable which is provided by the deployment configuration

Allowing anyone to access the server proved annoying too: The folowing configuration works
```

resource "google_cloud_run_service_iam_member" "noauth" {
  location = google_cloud_run_v2_service.leios_server.location
  service  = google_cloud_run_v2_service.leios_server.name
  role     = "roles/run.invoker"
  member   = "allUsers"
}

```

but note that it does not have a `_v2_` tag! This was the mistake I made, I used a v2 iam_member with `name` proeprty which proved to be incorrect.
Invalid argument `2024-07-11'

### Weekly update

* initial design was geared toward optimal usage of bandwidth
  * => bandwidth is large, and it can accomodate spikes, so perhaps focus on something simpler?
  * developed a short pipeline which is much simpler
  * assumes 40% of bandwidth and needs to tolerate spikes (2.5x average throughput), provides same security, consume bandhwidth ~ throughput
  * seems ideal for pricing model based on volume

* could there be a use case for blob leios in the partner chain space?

## 2024-07-04

### Network pricing

Did some quick research on network pricing for a few major Cloud or VPS providers: https://docs.google.com/document/d/1JJJk4XPqmP61eNWYNfqL8FSbKAF9cWazKWFZP6tMGa0/edit

Comparison table in USD/mo for different outgoing data transfer volumes expressed as bytes/seconds and similar VMs (32GB RAM, 4+ Cores, 500GB+ SSD disk). The base cost of the VM is added to the network cost to yield total costs:

| Provider     | VM     | 50kB/s | 125kB/s | 250kB/s |
|--------------|--------|--------|---------|---------|
| DigitalOcean | $188   | $188   | $188    | $188    |
| Google Cloud | $200   | $213.6 | $234    | $268    |
| AWS          | $150 ? | $161.1 | $177.9  | $205.8  |
| Azure        | $175   | $186   | $202    | $230    |
| OVH          | $70    | $70    | $70     | $70     |
| Hetzner      | $32    | $32    | $32     | $32     |

Notes:

* the AWS cost is quite hard to estimate up-front, obviously on purpose. The $150 base price is a rough average of various instances options in the target range
* Google, AWS and Azure prices are based on 100% uptime and at least 1-year reservation for discounts

### Weekly meeting

* There's a simplified pipeline being worked on from Matthias -> shortens pipeline assuming we don't want to go above 0.4 Capacity
  * GP to share draft once available
* what about Blob leios?
  * Not much progress, we want to have a working simulation/PoC to be able to discuss over some concrete numbers with potential users
* there's a research stream started on incentives for storage
  * need to check with realistic cost models
  * Also need to take into account both rate and volume (typically for network usage in DCs, both are capped but one pays a linear fee for the later)
* SNARKs research
  * block producer generates a proof that other nodes can be verified
  * current: All voters verify the IBs => nr of voters is large so almost everyone is verifying
  * future: create proofs from IB producers that the IB is correct wrt ledger rule (mostly stage 2, smart contracts)
  * related to midnights
  * just have the heavy stuff (smart contracts)
* Ricky's comments:
  * how to guarantee different tx end up in different IBs?
  * sharding seems easier to solve than increasing throughputs?
* Tx diffusion not very well suited for Leios ?
  * need more work on mempool and network protocol for TXs

## 2024-06-25

### Blob Leios

As an intermediate deployment step a transient-data sharing version of Leios is being discussed, called "Blob Leios".
In Blob Leios, IBs contain unstructured data (that is not parsed by the blockchain's virtual machine) instead of transactions.
The IBs are expected to be retained by the SPOs for a limited amount of time, e.g., 2 weeks.
The virtual machine only parses a commitment to the data that is persistently stored by SPOs and allows for
the applications discussed in the  2024-06-20 logbook entry.

This approach defers dealing with a number of throughput scaling issues, such as :
* increased storage size
* concurrency issues that have to do with the concurrent generation of IBs (duplicate transactions, conflicting transactions)
* increased CPU requirements due to the validation of transactions included in IBs

thus making a first deployment of Leios a lot easier.
Note, that Blob Leios includes several new design elements such as:
* the freshest first network approach
* block voting
* the IB/EB/voting pipeline.

Finally, while the idea is similar to Ethereum's blobs, Leios allows scaling "data throughput" to an lot larger level than Ethereuem.


## 2024-06-20

### Team Meeting

From discussion with researchers about voting with Leios, it seems that:

* "Blob leios"  could be useful for Bulletin Board, adding some extra security
* Catalyst could be a good customer:
  * large number of votes (300k), would SPO be willing to serve that data?
  * having commmitment on chain is good as one can "complain" on-chain
  * Leios offer censorship freeness on top of availability
* Other possible use cases:
  * Governance actions could be more relevant: Small number of votes and actions, transient data?
  * auctions would be another good use case for "Blob Leios"
* Incentives for SPOs to serve the data?
  * in filecoin, serving data has a cost
  * compare w/ filecoin?
* We might need to allocate bandwidth to different protocols as Ouroboros, Mithril, Peras, Leios... will compete for the same network resources
  * in Leios, it's assumed there's minimal b/w reserved for votes/certificates and the rest is used for IBs

### Presentation by Sandro

Sandro gave us an introductory talk about Leios, motivating the decisions behind the details of the protocol.
The recording is available on GDrive: https://drive.google.com/file/d/1r04nrjMtHijJNTLW3FuE5vEu_y3a0ssi/view

## 2024-06-17

### Network Simulation for Leios

Discussing with researchers on some early simulations that are being worked on for Leios.

* Constraint: Setup threshold on _egress_ bandwidth, then simulate diffusion of a block to downstream peers
  * upstream sends notificatoin (Eg. header)
  * downstream asks for block body if it does not have it
  * then it "validates" (simulated time) and advertises to neighbours
  * process is repeated until all peers have received the block
* in the modeling of b/w limit, it does not multiplex connection bw
  with neighbours, e.g it send each block to one node at a time,
  consuming a fraction of the available b/w for each single
  transmission until maximum is reached
* simulate 1000 nodes and then plot the number of nodes who have not received the block at time $t$
  * send 500 blocks with different rates (from 1/s to 1/ms)
  * δ = 8 (4 inbound, 4 outbound)
  * b/w limit = 1Mb/s
  * block size ~ 1kB
* when sending 10 blocks/s we observe more variation, a bit more contention as the  _freshest first_ policy starts to kick in
* at 1block/ms there's a much wider variation in time it takes to reach nodes
  * the first blocks take the longest as the queues are filling up with fresher blocks
  * latest blocks go faster, almost as fast as when rate is much slower, but this is also an artifact of the simulation (eg. time horizon means there's no block coming after which decreases contention)
* some enhancements:
  * we want to model w/ larger blocks
  * need to notify neighbours when a block is received to stop waiting
  * validate results and clean-up model

## 2024-06-13

### Weekly meeting

* Eth has blobs with a 2-weeks TTL: https://vitalik.eth.limo/general/2024/03/28/blobs.html
  * https://www.eip4844.com/
* Leios could be used to store other data than tx -> put unstructured data, possibly transient
* Intermediate state where we accomodate transient unstructured data
  * easier to build and deploy -> no need for concurrency/tx validation/CPU
* Concurrency issues?
  * conflicting txs, duplicates detection
* optional Leios node?
  * how much miners could ignore Leios blocsk? Security issues
  * use case = votes?
* Leios would support much more data than Eth >>> MBs
* Make Leios certificate verifiable on-chain through Plutus?
  * Requires BLS keys and signatures?

Next steps:

* [ ] Identify potential use cases for "transient data" Leios
* [ ] Keep working on protocol model

## 2024-06-10

### Meeting w/ Spyros

Spyros will work this week on network simulation for Leios

* Uses discrete event simulator [Peernet](https://github.com/PeerNet/PeerNet) to play and replay specific scenarios
* Setting bandwidth as a limiting factor (upload/download), need to change some parameters
  * need to work at protocol messages
  * TCP is not explicitly modelled in the simulator
* Goal:
  * check whether theoretical analysis matches practical experiments?
  * what's limit for block generation frequency?
* if bandwidth is not saturated, everything's fine
* if bandwidth is saturated:
  * need to queue local actions according to bandwidth availability
  * main input parameter is IB generation rate
  * output = delivery ratio of IBs
  * if IB rate > threshold -> most blocks won't make it because of _freshest first_ policy

Next steps:

* [ ] SV: work on simulation at the IB level
* [ ] SV: Share code when available
* [ ] All: Reconvene next monday to discuss how to publish results

## 2024-06-06

### Structuring repository for Open-source

* Added basic instructions for [Code of conduct](CODE-OF-CONDUCT.md), [Contribution](CONTRIBUTING.md) guidelines, and some [coding standards](CODING-STANDARDS.md).
* Restructured code to merge `leios` and `leios-sim` package in a single one as it's pointless to maintain to different simulators
* In passing, I reformatted all code following new coding standards (eg. using fourmolu), including cabal files

## 2024-05-31

### Designing test environment

We sketched some ideas on how to approach the problem of exploring the behaviour of Leios w.r.t. networking as discussed yesterday, and came up with the following high-level design:

![](images/leios-network-simulation.jpg)

## 2024-05-30

### Leios meeting

* simulate full network is more interesting
  * freshest first approach is important!
  * modelling changes in delays
* tx throughput -> lots of problems
  * easier to talk about throughput of IBs
  * measure actual bandwidth
  * CPU vs. Network bottleneck
* certificates  for EBs -> a committee, also vote on the correctness of data
  * provides stage 2 validation at a limited cost
  * IB producer proofs the block is correct
* TODO:
  * network simulation of the protocol -> showing latency is not an issue -> need to model it!
  * ΔQ model of the pipeline
  * gather numbers about network latency/throughput across the globe
  * numbers of CPU consumption
* if data bandwidth is not limiting factor -> tx conflict might not be such a problem
  * network latency is not a limiting factor
* what's the impact of Leios at the edges of the network?
  * mithril?

* relation b/w latency and throughput
  * tp closer bw => latency to grow => takes more time to absorb spikes

## 2024-05-29

### Visualising node behaviour

* Added a simple web server rendering the throughput of IBs and EBs to basic Leios simulation
  * It uses `Tracer` interface to have the simulation code send JSON-formatted traces that are retrieved by the server and exposed through a WS interface.
  * The UI connects to the WS, retrieves the data and plots in on a live graph

> [!NOTE]
> Interface for building `Tracer` in [contra-tracer](https://hackage.haskell.org/package/contra-tracer-0.2.0.0/docs/Control-Tracer.html) changed to use a Arrow-based datatype.
> The `newtype Tracer` now wraps a `TracerA`rrow data type that looks conceptually like:
>
> ```
> data TracerA m a where
>  Emitting :: (a -> m x) -> (x -> m b) -> TracerA m a b
>  Squelching :: (a -> m b) -> TracerA m a b
> ```
>
> with some `Kleisli` wrappers omitted for readability reasons.

![](images/draft-leios-ui.gif)

Some Ideas for a better model:

* Define the max bandwidth (in bytes / round) for the node
* Within a round, a node can receive + send this max number bytes
  * In input, deliver to the node all the proposed blocks (freshest first) until the max bandwidth is reached (or the number of offered blocks is exhausted?)
  * Same for output
* IB burst is dealt with by freshest first: An adversary can only accumulate "old" blocks which won't be fetched and trumped by newer ones
  * This is guaranteed by sortition voting which is verified in the block header
* We should model the various messages exchanged at each step of the pipeline and see what happens with various values of λ and max bandwidth

## 2024-05-28

### Discussion w/ Nicolas

* We tried to get a better intuition at Leios, following [Sandro's slides](https://docs.google.com/presentation/d/1W_KHdvdLNDEStE99D7Af2SRiTqZNnVLQiEPqRHJySqI/edit#slide=id.g2df51b2cf33_0_950) focusing on the IB -> EB construction.
* We wrote some code modelling a single node, along with an input queue for IBs and an output queue for EBs
* It's not obvious how the various parameters and constraints interact and what exactly we want to model
  * We start with a "happy path" behaviour where we input at most $C * λ / (λ + 1)$ IBs every round, and every such IB as the correct round number
  * We would like to model adversarial behaviour, eg. burst, equivocations, etc.
* What is it that we want to check? That an EB contains all the "right" IBs?

Code is in the [leios](leios/) directory

### Quick discussion with Sandro

We were supposed to shoot some made-up scenes where we would be working and drawing things, so we figured we could as well take this opportunity to ask questions to Sandro about the small experiment we did in the morning.

Here is some draft we drew:

<img align="left" src="https://github.com/input-output-hk/ouroboros-leios/blob/9c8ff6c62fbd7ae3bed12d75abb8e4ed783d59dc/images/zurich-leios-draft.png#L1" width="50%" />

Couple explanations:

* Upper part is about _equivocation_, eg. an adversary producing different IBs at the same slot.
  * a node will observe the equivocation (on the far right) by being offered 2 _equivocated_ headers from different peers
  * This node will be able to produce a _proof of equivocation_ that's useful when voting for IBs (and EBs?)
* Lower part is about _freshest first_ download policy: Two nodes producing valid IBs at different slots.
  * given the choice of headers (and bodies) consumer node will choose to download the freshest body first, eg. B in this case
  * headers are downloaded in any order as we can't know whether or not they are "freshest" before reading them
  * It seems that's only relevant if there are more blocks offered than available bandwidth :thinking:

## 2024-05-24

### Meeting w/ Research

What's been going on for Leios in the past year?

* mostly research work
* gaining confidence from a research perspective
* there's some unfinished business which needs engineering collaboration, the most important one being networking
  * ranking blocks + input blocks -> IB dominate the bandwidth
  * nodes download blocks w/ newest VRF timestamp
  * blocks in praos need to reach everyone in 3s, IB can take longer
  * praos is CPU bound -> sidestep CPU bottleneck
* testing w/ different scenarios to compare Praos and Leios
* network part -> self contained
* Goal: Define a ΔQ model for Leios which we can "play" with
  * What's the latency for blocks delivery?

* On the protocol structure:
  * not fit for production, geared towards solving research problems
  * need to do a bit tweaking
* simple Leios vs. full Leios: Build a simple model first

* follow-up publication?
  * network part -> some progress
  * mempool -> how tx diffusion happens?
  * avoiding including tx in different input blocks

* attack: validate tx multiple times w/o paying fees
* impact of multiple IB/txs on the ledger? -> UTxO model

* separate leios layer from consensus layer -> only impact consensus w/ certificates
  * test IRL with CF?

## 2024-05-21

* Invited team to the existing repository containing Duncan's initial simulation work and technical report for CIP publication
* Started logbook :)

## 2024-05-16

### Kick-off meeting

* Renate from Consensus team will be the main person working full time on this in a  "Prototype engineer" role
* Arnaud will be helping her, looking for synergies with the work we do in Peras
* Giorgios will be research liaison
* We have scheduled a weekly working session every Thursday at 2pm CET, the first occurence of which happened today.
* Next step will be to build a model of Leios in code in order to better understand how the protocol works in a broad brush way
* Wealso want to look at previous work done by Duncan  both in the design document and the network simulation he built
* Today we also touched lightly on the topic of modelling Leios using Delta-Q: It seems the Leios pipeline described in the paper lends itself nicely to such kind of performance modelling
