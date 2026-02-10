# Mathematical model of the memory pool

This document describes a simple mathematical model of the Ouroboros memory-pool behavior, and suitable for idealized analyses of Praos and Leios. We apply it to the problem of memory-pool poisoning by adversarial nodes that attempt to front-run honest transactions that they receive.

## Variables

| Symbol      | Units     | Description                                     |
| ----------- | --------- | ----------------------------------------------- |
| $`\delta`$  | s/hop     | Per-hop diffusion time                          |
| $`\alpha`$  | block/s   | Active slot coefficient                         |
| $`\sigma`$  | tx/s      | Transaction submission rate                     |
| $`b`$       | kB/tx     | Typical transaction size                        |
| $`B`$       | kB/block  | Block size                                      |
| $`\kappa`$  | kB/s      | Blockchain capacity                             |
| $`\rho`$    | 1         | Relative tx load                                |
| $`\lambda`$ | hop       | Effective number of hops                        |
| $`\tau`$    | s         | Typical diffusion time                          |
| $`N`$       | node      | Number of nodes in network                      |
| $`k`$       | link/node | Typical upstream or downstream degree of a node |

## Basic relationships

- Blockchain capacity: $`\kappa = \alpha \cdot B`$.
- Data rate: $`\sigma \cdot b`$.
- Effective load: $`\rho = \frac{\sigma \cdot b}{\kappa} = \frac{\sigma \cdot b}{\alpha \cdot B}`$.
- Characteristic diffusion time: $`\tau = \lambda \cdot \delta`$.

## Estimating the typical diffusion time

Start with the assumption that the Ouroboros topology approximates a *directed* [regular random graph](https://en.wikipedia.org/wiki/Random_regular_graph) (RRG), which aims to have the optimal information-transmission characteristics of a [Ramanujan graph](https://en.wikipedia.org/wiki/Ramanujan_graph). The Ouroboros network design documents[^1] do not state this explicitly, but it is a consequence of the churning of hot/warm/cold peers and targets and constraints on the number of peers. In particular, that scheme prevents the Ouroboros topology from becoming a [scale-free network](https://en.wikipedia.org/wiki/Scale-free_network): instead, the upstream or downstream degree of a node tends towards a typical value, which we idealize as $`k`$.

Consider the diffusion of a transaction from the node where it is submitted to the rest of the nodes. Let $`h_i`$ be the number of nodes it has reached in the $`i`$th hop and $`H_i = \sum_{j=0}^i h_j = H_{i-1} + h_i`$ be the cumulative number of nodes it has reached by the $`i`$th hop. The transaction starts with $`h_0 = 1`$ and $`H_0 = 1`$. For a directed RRG the expected number of hops will be

$$
E \left[ h_{i+1} \right] = \left( N - H_i \right) \left( 1 - \left( 1 - \frac{1}{N} \right) ^ {h_i k^\prime} \right)
$$

where the effective degree $`k^\prime = k - \frac{k}{N - k} = k \cdot \frac{N - 2}{N - 1} \approx k`$, for large $N$, accounts for possibility that a downstream peer is also an upstream peer. The first factor represents the number of nodes to which the transaction has not already diffused and the second factor is the probability that at least one of the $`k^\prime`$ neighbors of the $`n_i`$ nodes hasn't received the transactions. If we replace the expectation by $`h_{i+1}`$ itself, then for large $N$ we can approximate the cumulative number of nodes diffused to as

$$
H_i = \frac{N}{1 + \left( \frac{N}{H_0} - 1 \right) k^{-i}} ,
$$

which happens to be a [logistic distribution](https://en.wikipedia.org/wiki/Logistic_distribution) with mean $`\log_k N`$ and scale $`(\ln k)^{-1}`$. Under the RRG assumption we have $`\lambda = \log_k N`$.

For Cardano `mainnet` the recommended active peers[^2] is $`k = 20`$ and there are roughly $`N = 25000`$ nodes participating in the network. The recursion relation yields a mean number of hops of $`3.75 \text{ hops}`$, but the approximate method yields a mean $`\log_k N \approx 3.44 \text{ hops}`$ and standard deviation $`\frac{\pi}{k \cdot \sqrt{3}} \approx 0.61 \text{ hops}`$. The following plot illustrates that the recursion relation yields a more rapid diffusion and saturation. This roughly agrees with the anecdotal diameter of five or six for `mainnet`: the transaction reaches 24% of the network in three hops and 99% of it in four hops. A reasonable value for the typical number of hops for transaction diffusion is $`\lambda = 4 \text{ hops}`$.

![Transaction diffusion on a directed regular random graph with k = 20 and N = 30,000](./diffusion.svg)

## Poisoned memory pools

Now consider the scenario where there is a fraction of the nodes, $`p_\text{adv}`$, are adversarial in that when an adversarial node receives a transaction, it _does not announce it to its upstream peers_: instead, it creates a new, conflicting transaction and announces that instead. This scenario aims to mimic front-running or MEV (miner extractable value): the adversarial node replaces each transaction with one to its own advantage. _In real life, of course, only a fraction of transactions (arbitrage opportunities, entries in order books, etc.) might be susceptible to such front running._

The front-run transactions compete with the original honest ones to diffuse faster to the block-producing node. Because the honest and front-run version of the transaction conflict with one another (i.e., consume at least one common input), only one of them can be accepted into a node's memory pool. Honest nodes accept transactions on a first-come first-serve basis, but will not accept a transaction that conflicts with its memory pool. We consider a memory pool to be "poisoned" if it contains the dishonest replacement of the transaction. Under the RRG assumption, the probability of an honest memory pool having been poisoned is the sum up to the graph's diameter of the fraction of nodes a given number of hops away times the probability of any intermediate node having been poisoned:

$$
p_\text{poison} \approx \sum_{i=1}^\lambda \frac{h_i}{N - 1} \left( 1 - \left( 1 - p_\text{adv} \right) ^ {i - 1}) \right) \approx 1 - \left( 1 - p_\text{adv} \right)^{\lambda-1} .
$$

For a small fraction of adversaries, this reduces to $`p_\text{adv} \cdot (\lambda - 1)`$.

[^1]: See [Introduction to the design of the Data Diffusion and Networking for Cardano Shelley](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-design/network-design.pdf) and [Ouroboros Network Specification](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf.).
[^2]: See [the default mainnet configuration file for cardano-node](https://github.com/IntersectMBO/cardano-node/blob/9cf1e651e9fc3726a5fa9771b0d3479e5b909c6b/configuration/cardano/mainnet-config.yaml#L49).
