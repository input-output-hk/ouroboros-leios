# Modeling resource constraints and interdependencies

Develop a model of the constraints, dependencies, scheduling latitude for critical operations such as message transfer and cryptography.

Timeline:
- *December:* analysis of empirical data and construction of statistical models.
- *January:* mathematical models.
- *February:* executable models.
- *March:* assemble technical report.
- *March 11:* end of 100-day cycle.

## Motivation

Leios is more CPU- and network-intensive than Praos, but it also has a larger time budget to accomplish the numerous tasks in the protocol. Up to now, the viability of resource usage has only been verified empirically via the two Leios simulators. Developing an analytic model (a constraint model that is computable) will make it possible to reason about Leios’s resource usage in both the optimistic and adversarial cases and to assess its safety. Such a model is needed to inform the discussions about setting Leios protocol parameters and safety margins.Deeper understanding on how much of the mempool can be partitioned by a network attacker.

## Customers

The Linear Leios engineering effort and the broader technical community can use the products of this work to help set protocol parameters and bound the resources required for Linear Leios. The model could become part of a “protocol parameter and security” dashboard like the one being developed by the Peras engineering team.

## Outcomes

1. Statistical models of ledger operations.
2. Mathematical model that relates Leios operations and phases (and associated protocol parameters) to the resource budgets (network, CPU, and I/O) available for meeting various transaction loads.
3. A computable embodiment of that model in Agda, Lean, or other suitable platform.
	1. The statistical model and, to some extent, the mathematical model will be suitable for use in the DeltaQSD effort for Linear Leios.
	2. The executable model will be suitable for optimization and feasibility studies.
4. Example computational experiments demonstrating the models usage for computing resource budgets and identifying bottlenecks.

## Tasks

### Empirical foundations on Cardano mainnet

- [ ] Measure `Apply`, `Reapply`, and their difference for all mainnet transactions.
- [ ] Estimate available bandwidth.
- [ ] Estimate typical latencies.

### Modeling resource constraints

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

### Stretch goal

- [ ] Improve granularity of ledger-operation measurements by `db-analyser` tool.
