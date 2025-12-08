# [#664](https://github.com/input-output-hk/ouroboros-leios/issues/664) Analysis of the mempool partitioning attack

What are the costs and benefits from the adversary’s perspective when considering attack vectors that cause the honest nodes’ mempools to not overlap.

Timeline:
- *December:* analysis of empirical data and construction of statistical models.
- *January:* mathematical models.
- *February:* executable models.
- *March:* assemble technical report.
- *March 11:* end of 100-day cycle.

## Motivation

Part of the motivation for the Linear Leios indirection in EB bodies versus EB closures is the assumption that honest nodes’ mempools usually mostly overlap. If this is assumed to be common, then it might also justify decreasing $L_\text{vote}$, for example.

## Customers

In addition to informing research and networking experts, memory pool modeling and scenario analyses will help inform the community as to safe setting of protocol parameters.

## Outcomes

1. Statistical models of the memory pool and its correlations.
2. Mathematical model of mempool operation under optimistic and adversarial conditions.
	1. The statistical model and, to some extent, the mathematical model will be suitable for use in the DeltaQSD effort for Linear Leios.
	2. The executable model will be suitable for optimization and feasibility studies.
3. A computational embodiment of the mempool model.
4. Analyses of adversarial memory pool simulations.

## Tasks

### [#637](https://github.com/input-output-hk/ouroboros-leios/issues/637) Empirical foundations on Cardano mainnet

- [ ] [#644](https://github.com/input-output-hk/ouroboros-leios/issues/644) Mempool telemetry experiment
	- [ ] Probability that a transaction is in one node's mempool, given that it is in another node's mempool.
	- [ ] Probability that a transaction is in the node's mempool, given that it is later received in a block.
	- [ ] Probability that a transaction is in a block received by a node, given that is was previously received in the node's memory pool.
	- [ ] Distribution of a transaction's arrival time prior to the slot where the block was produced.
	- [ ] Fraction of mempool transactions received in the node's mempool before in their block.
	- [ ] Temporal autocorrelation of fraction of mempool transactions received  in the node's mempool before in their block.
	- [ ] Temporal and spatial autocorrelation of fraction of mempool transactions received in the node's mempool before in their block.
	- [ ] Identification and filtration of node clusters of mempool correlation.
	- [ ] Tracking of CF's "canary" transactions' arrival in memory pools.
	- [ ] Tracking of natural and induced congestion on arrival in memory pools.
- [ ] [#645](https://github.com/input-output-hk/ouroboros-leios/issues/645) Transaction analysis
	- [ ] Fraction of transaction spent in the block they were created.
	- [ ] Distribution of transaction lifetime (blocks and slots).
	- [ ] Distribution of length of transaction chains in consecutive blocks.
- [ ] [#646](https://github.com/input-output-hk/ouroboros-leios/issues/646) Block analysis
	- [ ] Distribution of block utilization.
	- [ ] Temporal autocorrelation of block utilization.
	- [ ] Temporal autocorrelation of highly utilized blocks.
- [ ] [#647](https://github.com/input-output-hk/ouroboros-leios/issues/647) Peer telemetry experiment and CF topology dataset
	- [ ] Geographic distance of block or transaction providers.
	- [ ] Distribution of frequency of block or transaction provision by downstream nodes.
	- [ ] Persistence (temporal autocorrelation) of active peers.
	- [ ] Number of active peers.
	- [ ] Frequency of out-of-ASN and out-of-region hops.
	- [ ] Connectivity matrix heat map.
	- [ ] Filtration of topological components by long hops.

### [#667](https://github.com/input-output-hk/ouroboros-leios/issues/667) Modeling the memory pools and their spatio-temporal correlations

- [ ] [#668](https://github.com/input-output-hk/ouroboros-leios/issues/668) Regression models of mempool behavior under normal operating conditions.
	- [ ] Coherence between local and global memory pools.
	- [ ] Variability of mempool synchronization.
	- [ ] Time delays between transaction arrival and block arrival.
	- [ ] Frequency of long hops.
- [ ] [#669](https://github.com/input-output-hk/ouroboros-leios/issues/669) Mathematical model of memory pool behavior.
	- Model definition.
		- Independent variables.
			- Network topology.
			- Probabilities derived from the aforementioned regression models.
			- Honest and adversarial stake distributions.
		- Dependent variables.
			- Coherence (degree of partitioning) of memory pools globally.
			- Number of previously unseen transactions that must be fetched after an EB arrives.
			- Fraction of EBs missed because transactions were not seen soon enough.
			- Fraction of RBs missed because transactions were not seen soon enough.
	- Analytic questions:
		- How does fragmentation of the memory pool (either under typical or adversarial conditions) interact with resource requirements and protocol parameters?
		- To what extent can memory-pool fragmentation stop the production of EBs or impact Praos?

### Stretch goals (uncommitted)

- [ ] Simulator that is approximately faithful to the node's p2p network logic.
