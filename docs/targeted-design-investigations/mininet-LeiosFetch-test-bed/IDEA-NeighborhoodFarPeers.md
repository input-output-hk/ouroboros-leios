## Introduction

This memo proposes some requirements for the LeiosFetch decision logic, derived from the design of Cardano's P2P mechanisms.

The new insight that motivates this document is that the intended network dynamics across the topology inform not only the algorithm for selecting peers but also the algorithm for allocating resources among the selected peers.

## Observation 1

Cardano architects leveraged technical reports from [Spyros Voulgaris](https://acropolis.aueb.gr/~spyros/) et al of Athens University of Economics and Business when designing the P2P peer sharing and selection algorithm.
A key recommendation from these reports was that a significant fraction of a node's peers should be low latency and another significant fraction should be high latency.
(Choosing the "high latency" fraction of peers randomly instead of actually considering their apparent latency seemed to be just as effective and has the added benefit of mitigating the attacker who pretends to have higher latency.)
The intended dynamics are for intercontinental peers to first deliver a message between distant neighborhoods, and then the low latency connections would ensure the message rapidly spreads within each neighborhood.
And the current Cardano peer selection scheme has been observed to achieve those dynamics in the following way, according to personal communication with Marcin Wójtowicz.

> Each node has a relatively sparse/small valency (eg. 10C10R from the AUEB reports) so to "ensure" prompt long distance transfer we want to grow our local cluster with some fraction of low RTT peers, such that this cluster as a whole has a high probability of direct connection to far away peer(s) by randomness alone / the random fraction of peers at each relay. The latter achieves the intended outcome for the cluster.

## Observation 2

Peers with low latency can utilize resources (e.g. kernel buffers, shared network bottlenecks, etc.) more efficiently than peers with high latency.
Two concrete examples:

- The timeout for a request-reply exchange can be much tighter on a low latency connection.
  (TODO even if the timeout is fatal, ie causes disconnection?)

- The fetch decision logic can afford to aggressively limit the cumulative size of the outstanding requests for a low latency peer.
  In other words, their Bandwidth-Delay Product is low.
  (Actually, they could still have a large BDP, but only if the bandwidth is very high.
  In that case, it would be affordable to not rely on fully saturating that bandwidth capacity.)

## Proposal

Those two observations together justify the following resource-efficient scheme for LeiosFetch decision logic.

- Do not send redundant requests (a.k.a. _hedge requests_) to high-latency peers.
- A request to a high-latency peer should request as much (useful) data as possible (e.g. all missing transactions from the EB closure).
  This ensures the sender will utilize as much of the link's bandwidth capacity as possible (i.e. up to the large Bandwith-Delay Product/Mathis ceiling/etc) instead of being unnecessarily application-limited.
- A request to a high-latency peer must have a relatively generous timeout, something like 1 second.
  Once that timeout fires, the node should switch its requests to a different high-latency peer.
- In contrast, requests to a low-latency peer should request a limited cumulative amount of data (and hence resource utilization) and a tight timeout.
  This allows a decomposable payload (like a EB closure) to be split among requests to multiple low-latency peers simultaneously.
  Only once the set of still-missing components is small enough for a single request would it be useful to send redundant requests to multiple peers, in order to prevent an adversarial peer from slow lorising the final missing piece.
  As a result, only a small amount of data would be requested more than once among low-latency peers.

**Risk**.
If the adversary can increase the probability of it being the first high-latency peer to offer some datum to all nodes in a neighborhood, then they could be a slow loris such that _none_ of the nodes in that neighborhood receive the datum from a high-latency peer.
The whole neighborhood would be delayed by at least one timeout and potentially more.

If that risk is unarmed, then some node in the neighborhood will promptly receive the payload from a high-latency peer, and then it will spread quickly among the neighborhood.
It's as if all of the nodes in the neighborhood shared their collective high-latency peers.
So, unless the risk above is armed, each neighborhood can only be temporarily deprived of messages originating outside the neighborhood if _all_ of the nodes in that neighborhood happen to choose a slow loris peer.
(Once it times out, then at least one neighbor will request it from an honest high-latency peer.)

The key ideas are as follows.

- Utilize multiple low-latency peers simultaneously, with a relatively small amount of outstanding data for each peer at any given time.
- Send overlapping requests to multiple low-latency peers only when constructing enough requests to saturate a low-latency peer would otherwise be impossible.
- Do not utilize multiple high-latency peers simultaneously---their dynamics require large requests and so utilizing multiple would require requests to overlap too much.
- TODO Somehow avoid making it too easy for an attacker to arrange for every node in a neighborhood to choose a slow loris attacker as the one high-latency peer they utilize.
  For example, the slow loris attacker could arrange to be the first high-latency peer to offer the block (e.g. even before they have it).
    - On the one hand: you want to request the block from the first peer that offers it to you; if they're honest, then it's just extra latency to not immediately request it.
    - But the adversary can arrange to be that peer.
    - So some nodes would have to (randomly) wait for additional high-latency peers to offer them the same payload, and only react to the second (or even third) offer?
    - If one node in the neighborhood _doesn't_ have that attacker as peer, then the risk is already mitigated.
      How to determine if that's already sufficient likely?
      If it is, then every node could simply request the payload from the first high-latency peer to offer it.
- TODO We're tacitly assuming that it's not worth the complexity/inefficiency for LeiosFetch to ensure that even a node that doesn't have any honest low-latency peers will receive EB bodies and closures promptly.

TODO so the optimistic logic is:

- Consider low-latency and high-latency peers independently.
    - (The only interaction among low- and high-latency peers is that data that has already _arrived_ from one doesn't need to be requested from the other.)
    - TODO how to assess whether a peer is low- or high-latency?
      Just some (bandwidth-independent?) (load independent?) RTT cutoff Y (TODO tune Y)?
    - TODO does that assessment need to change over time?
- For low-latency peers:
    - Never have more than X outstanding bytes of requests sent to a single low-latency peer (TODO tune X).
    - Only start sending overlapped requests among low-latency peers once there are ≤X bytes of the payload missing---i.e. once the non-overlapped requests could no longer saturate X.
- For high-latency peers:
    - Immediately request all of the still-missing portion of the payload from the first high-latency peer to offer it.
    - Don't request any part of that payload from another high-latency peer until the first request times out.
      (TODO is that timeout necessarily fatal?
      If it's not fatal, then the network resources (including the kernel buffers) might not actually be free yet… but at least the application-level buffers would already be free?)
    - Note that we need to send the request even if *some* of the data has already arrived from low-latency peers---the high-latency peer might be the only one that will actually send _every_ part of the payload (i.e. might be the only honest peer).

## Conclusion

A fetch decision logic that definitely utilizes any and all of its low-latency peers, both promptly and fully, will essentially inherit the high-latency honest peers of its low-latency honest peers.
Therefore, we don't need that logic to _also_ definitely utilize any and all of its high-latency peers promptly and fully---as long as at least *one* node in each "neighborhood" happens to utilize one of its high-latency peers promptly and fully, then the whole neighborhood benefits from that with minimal additional latency.
