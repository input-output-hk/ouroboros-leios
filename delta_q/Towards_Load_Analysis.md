# Towards Load Analysis

The focus of published work on ΔQSD (that I’m aware of) is to model the timeliness of outcomes without resource constraints, with strong results on algebraic equivalences to help with efficient expression evaluation.
Within the context of Ouroboros Leios we very much need to model resource constraints and their non-linear effects on timeliness, though, because the focus of that work is to approach as closely as possible the allocated network bandwidth of the system — which implies that resources will frequently be used at their limits.

> This article documents my journey in understanding how ΔQSD can be used, with some missteps and wrong interpretations along the way.
> One important thing I learnt was that ΔQSD is meant only for timeliness analysis, complemented by load tracking _synthesis_.
> In other words, the effect of resource constraint is fed into the model, not an output of the evaluation of the model.

## High fidelity resource usage tracking

Timeliness analyses are performed while retaining full detail on possible executions; this is achieved by computing over cumulative distribution functions (CDF) instead of scalar values.
The choice operator then acts as splitting the probability mass to be distributed over the two branches according to their weights, sequencing adds delays by convoluting CDF, and synchronisation branches are combined using the rules for probability distributions.
It follows that a load analysis should be done in an analogous fashion, using cumulative resource usage distribution functions (CUDF) as atoms of computation; this obviously adds one dimension per resource to the problem that previously existed solely along the time axis.

An outcome is therefore represented as a function from time to a tuple of

- cumulative completion probability (same as previously)
- a vector of cumulative resource usage probability distributions

The rules for evaluating these richer outcomes add the following resource-related behaviour:

- sequence spreads out the load probabilities along the time axis by folding in the time domain, as for the completion CDF
- choice spreads the load probabilities along their respective load axis by letting probability mass flow through the outcome graph and correspondingly populate the resource usage probabilities
- synchronisation (∀ or ∃) performs two branches in parallel and thus adds loads (by convoluting their matching pairs of CUDF at each point in time)

From these observations it is clear that only synchronisation may potentially violate resource constraints (assuming that each individual outcome is constructed such that it respects its constraints, e.g. by using the local network link at 100% of its usable bandwidth).
A resource constraint would be formulated as a CUDF that acts as a lower bound for the actual CUDF at each point in time.
For example, a hard limit would be expressed by a step function that goes from zero to one at the available maximum.
The probability of a violation is then obtained by evaluating the computed CUDF at that maximum and subtracting the value from one.
The maximum demanded resource usage is given by the resource value at which the CUDF reaches one.
In case of a violation, the set of collaboratively violating outcomes needs to be transformed to express the effect of the resource constraint (e.g. sending across a network becomes slower and takes longer); or the resource demand it inflexible and thus the system fails (e.g. when more storage space is required than available).

The first issue with implementing the above is that resources may occur in multiple parallel branches of a ΔQ expression, which means that constraint violations cannot be recognised while evaluating an expression in bottom-up fashion in a fashion that is required to compute the outcome transformation.
Assuming that a constraint violation has been recognised, the appropriate response is to stretch or delay a resouce usage so that the constraint is respected — if the network or CPU is busy right now, further work will be finished later.
The second issue then is that some parallel branches of a ΔQ expression may be unaffected by the resource constraint violation and thus require no time stretching or delay: the effect of resource exhaustion is localised to one resource, which may affect some but not all branches.
Consider as example `∀(delay10 | useCPU)` where the delay depends only on wall clock time while the CPU usage may be subject to stretching or delay.
This means that a resource constraint violating discovered when combining this expression with some other expression needs to transform not the whole composite outcome but only `useCPU`, the result of which then needs to be combined again with the unaffected `delay10`.

## Possibly correct but horrible solution

> _(This section documents a misunderstanding of how ΔQSD should be used, so take it with a spoonful of salt)_

The above problems seem solvable by the algorithm described below, which makes my spidey senses tingle that predict unacceptable computational latency.

1. compute the CDF and time-dependent CUDFs without regard for constraints
2. search for the earliest point in time when a resource constraint is violated and identify the resources involved
3. identify all actually contributing outcomes in the expression (which may NOT be all outcomes using those resources!)
4. apply resource-dependent rules for how to transform the outcome’s completion and CUDFs to each of these outcomes and thus modify the graph
5. start from step 1 with the new outcome graph

It would be much nicer to somehow transpose the problem such that algebraic treatment allows the isolation of constraint violations and their treatment, but so far I have been unable to come up with such a solution.
The main blocker is that constraints live in their resource dimension but affect — partially! — the time dimension; it would be rather easy to just stretch the passage of time during resource constraint violations for the whole system, but this would be quite wrong, since the point of a distributed system is exactly the decoupling afforded by parallelism.

## Resources are localized

One further complication is that each resource is associated with a specific location within the system: sending bytes from A to B does not exhaust resources at C.
Resource usage of an outcome thus must be labelled with either the input or output events for that outcome, assuming that each event belongs to exactly one location — this is a reasonable assumption for any accurate model of a distributed system, where all information is subject to local availability.
This means that modelling the diffusion of data across the network requires tracking resources at a couple thousand locations, and it means expanding the expression modelling this activity to actually have a couple thousand branches instead of using the nice and simple choices between 1, 2, 3, 4 hops as used for the [earlier Peras model](https://peras.cardano-scaling.org/docs/reports/tech-report-1/#certificates-in-block-header).

It would be nice if a single diffusion activity could be computed once and then be uses in probabilistic fashion: the node under observation could be at any one place within the gossip flow tree.
Unfortunately we will want to simulate the interaction of overlapping pipeline instances, which may hit a given node at different times; adversarial behaviour may exacerbate this problem.
So for some analyses we may not be able to greatly simplify the outcome expression back to the 1, 2, 3, 4 hop model, which in combination with an iterative algorithm like the one sketched above smells like it will require substantial computational resources.
And this runs counter to the impetus for this whole work, which is to offer an _interactive_ tool to the whole community, both within and without of IOG.

## Good news everyone: focusing on timeliness is actually good enough

When presented with the difficulties above, a conversation with Neil & Peter from PNSol brought clarity and enlightenment:
ΔQSD isn’t meant to be used that way, it is meant to be driven by timeliness, and timeliness alone.

Instead of using load metrics to drive the evaluation of the model, the model is supposed to be evaluated only for timeliness _under the assumption that all resource constraints have already been included in the modelling_.
So the correct approach is to model resource usage in such a way that it already probabilistically delays some outcomes, avoiding that the resource will actually be exhausted _by design_.

As an example we now model the sending of network packets from a given network node over a given network interface.
Nominally, sending 1500 octets on a 1Gbps link takes 120µs, but we anticipate that there is a queue of depth ten in front of that interface that may already hold between zero and ten packets, leading to either a delay of up to 1.08ms or failure (if the queue is full).
We could thus model this outcome with a timeliness CDF that has ten steps and tops out at (1 − `failure`).

Now using this model in a larger expression, e.g. to express the Praos chain sync algorithm, will lead to a distribution of timeliness that reflects the assumed effect of the network queue.

The big question then is: do the assumed queue fill probabilities match actual system behaviour?

### Approach 1: measure

We could run the real system and keep tabs on the network interface queue usage to assess whether our assumption was correct.
This result will depend on the precise workload we put on the system.

### Approach 2: model it

We could also use the ΔQ expression itself to give us a hint as to how realistic our assumption was.
This requires the load tracking described in the sections above, which will then provide an answer for the probability distribution of the usage of each resource over time.

In the above example, we would attach the load metric “network interface on node X used” to the network sending outcome, with a value of one for the whole maximum duration of 1.2ms.
When the expression containing this outcome (potentially multiple times) has been evaluated with load tracking, we have for each point in time a probability distribution of how many times this network interface is being used in parallel.
Since we designed it with a queue depth of ten, exceeding ten parallel usages constitutes a resource constraint violation — we can then compare how often this occurs with the probability we assigned to the corresponding failure.
If the real system doesn’t actually fail in this case but just gets slower, we would respond to a violation by increasing the assumed queue depth until no violation occurs anymore.
It is at this point that ΔQ tells us _via the timeliness constraints_ whether the system is feasible under realistic load constraints.
