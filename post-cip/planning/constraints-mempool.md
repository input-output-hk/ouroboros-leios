# Leios ARC planning

Timeline:
- *December:* analysis of empirical data and construction of statistical models.
- *January:* mathematical models for resources and memory pool.
- *February:* executable models for resources, memory pool, and adversarial impacts.
- *March:* assemble technical report.

## Modeling resource constraints and interdependencies

Develop a model of the constraints, dependencies, scheduling latitude for critical operations such as message transfer and cryptography.

### Motivation

Leios is more CPU- and network-intensive than Praos, but it also has a larger time budget to accomplish the numerous tasks in the protocol. Up to now, the viability of resource usage has only been verified empirically via the two Leios simulators. Developing an analytic model (a constraint model that is computable) will make it possible to reason about Leios’s resource usage in both the optimistic and adversarial cases and to assess its safety. Such a model is needed to inform the discussions about setting Leios protocol parameters and safety margins.Deeper understanding on how much of the mempool can be partitioned by a network attacker.

### Customers

The Linear Leios engineering effort and the broader technical community can use the products of this work to help set protocol parameters and bound the resources required for Linear Leios. The model could become part of a “protocol parameter and security” dashboard like the one being developed by the Peras engineering team.

### Outcomes

1. Statistical models of ledger operations.
2. Mathematical model that relates Leios operations and phases (and associated protocol parameters) to the resource budgets (network, CPU, and I/O) available for meeting various transaction loads.
3. A computable embodiment of that model in DeltaQSD, Agda, Lean, or other suitable platform.
4. Example computational experiments demonstrating the models usage for computing resource budgets and identifying bottlenecks.

### Tasks

#### Empirical foundations on Cardano mainnet

- [ ] Measure `Apply`, `Reapply`, and their difference for all mainnet transactions.
- [ ] Estimate available bandwidth.
- [ ] Estimate typical latencies.

#### Modeling resource constraints

- [ ] Regression models for `Apply`, `Reapply`, and their difference.
- [ ] Mathematical model of constraints on Linear Leios.
	- Model definition
		- Independent variables.
			- Protocol parameters
			- Hardware resources/budgets, including parallelism.
			- Network resources/budgets.
			- Demand profile.
			- Adversarial strength.
		- Dependent variables.
			- Throughput achieved.
			- Fraction of EBs missed due to insufficient computational resources.
			- Fraction of RBs missed due to insufficient computational resources.
	- Analytic questions:
		- *Forward:* predict dependent variables from independent ones.
		- *Reverse:* estimate protocol parameters and hardware requirements for a specified level of performance.
		- *Mapping:* find boundaries around feasible regions of performance in parameter space.
- Executable realization of the mathematical model.
- Numerical study of feasible protocol parameters hardware requirements.

#### Stretch goal

- [ ] Improve granularity of measurements by `db-analyser` tool.

## Analysis of the mempool partitioning attack

What are the costs and benefits from the adversary’s perspective when considering attack vectors that cause the honest nodes’ mempools to not overlap.

### Motivation

Part of the motivation for the Linear Leios indirection in EB bodies versus EB closures is the assumption that honest nodes’ mempools usually mostly overlap. If this is assumed to be common, then it might also justify decreasing $L_\text{vote}$, for example.

### Customers

In addition to informing research and networking experts, memory pool modeling and scenario analyses will help inform the community as to safe setting of protocol parameters.

### Outcomes

1. Statistical models of the memory pool and its correlations.
2. Mathematical model of mempool operation under optimistic and adversarial conditions.
3. A computational embodiment of the mempool model.
4. Analyses of adversarial memory pool simulations.

### Tasks

#### Empirical foundations on Cardano mainnet

- [ ] Mempool telemetry experiment
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
- [ ] Transaction analysis
	- [ ] Fraction of transaction spent in the block they were created.
	- [ ] Distribution of transaction lifetime (blocks and slots).
	- [ ] Distribution of length of transaction chains in consecutive blocks.
- [ ] Block analysis
	- [ ] Distribution of block utilization.
	- [ ] Temporal autocorrelation of block utilization.
	- [ ] Temporal autocorrelation of highly utilized blocks.
- [ ] Peer telemetry experiment and CF topology dataset
	- [ ] Geographic distance of block or transaction providers.
	- [ ] Distribution of frequency of block or transaction provision by downstream nodes.
	- [ ] Persistence (temporal autocorrelation) of active peers.
	- [ ] Number of active peers.
	- [ ] Frequency of out-of-ASN and out-of-region hops.
	- [ ] Connectivity matrix heat map.
	- [ ] Filtration of topological components by long hops.

#### Modeling the memory pools and their spatio-temporal correlations

- [ ] Regression models of mempool behavior under normal operating conditions.
	- [ ] Coherence between local and global memory pools.
	- [ ] Variability of mempool synchronization.
	- [ ] Time delays between transaction arrival and block arrival.
	- [ ] Frequency of long hops.
- [ ] Mathematical model of memory pool behavior.
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

#### Stretch goals

- [ ] Simulator for the node's p2p network.
