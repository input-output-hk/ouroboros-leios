# Constraint model for Leios resource usage

## Scenario

1. The model starts at time $t_0 = 0$.
2. There are a total of $n_\text{cpu}$ CPUs.
3. The first event `RH` occurs after some delay, $\Delta t_\text{RH}$.
4. Then two sequences of events occur in parallel:
	1. `RB` processing:
		1. An event `RB` occurs after some delay, $\Delta t_\text{RB}$.
		2. Each `RB` contains $n_\text{RB}$ transactions that form a directed acyclic graph (DAG) rooted at the previous ledger state of unspent transaction outputs (UTxOs).
		3. The transactions must undergo cryptographic verification, and this can be done in parallel, with CPU delay $c_\text{verify}$.
		4. According to the partial ordering in the DAG, transactions must sequentially undergo ledger application, with CPU delay $c_\text{apply}$ after the cryptographic verification for the transaction is complete.
		5. When all of the DAG has been processed, the `RB` processing is considered to be complete.
	2. `EH` processing:
		1. An event `EH` occurs after some delay, $\Delta t_\text{EH}$.
		2. Each `EH` references $n_\text{EB}$ transactions that form a DAG that extends the DAG of the `RB`.
		3. In parallel each transaction referenced in the `EH`, which we call the `TBi` events, arrives after some delay $\Delta t_{\text{TB},i}$, where $i \in EH$.
		4. After a `TBi` arrives, it can be verified with CPU delay $c_\text{verify}$. All of the `TBi` verifications can be done in parallel.
5. `EB` processing occurs, potentially in parallel, as both `RB` processing and `EH` processing occur.
	1. According to the partial ordering in the DAG, transactions must sequentially undergo ledger application, with CPU delay $c_\text{apply}$ after the cryptographic verification for the transaction is complete. This processing can begin as soon as the "upstream" ledger applications (of the `RB` or `EB`) are complete.
	2. When all of the DAG has been processed, the `EB` processing is considered to be complete.
6. The `VT` event occurs after all of the above is complete, with CPU delay $c_\text{vote}$.
7. The model ends at time $t_1$.

Overall, we have a large DAG of computations where the `RB` event reveals the DAG, but the individual `TBi` events incrementally extend the DAG. The `TBi` events occur in an arbitrary, externally specified sequence after the `EH` event. The $c_\text{verify}$ process can occur completely in parallel after either the `RB` or `TBi` event, but the $c_\text{apply}$ process can only occur after the upstream part of the DAG is applied. All of the time delays and CPU delays are specified externally. We want to schedule the work subject to the $n_\text{CPU}$ constraint in order to minimize $t_1$.

