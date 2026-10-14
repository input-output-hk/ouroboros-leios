# Demo: Acceptance

Drives the production-grade Leios implementation, on ouroboros-consensus `main`, towards feature parity with the prototype. A production node takes a role in a prototype network, and what that network achieves shows how far the production node has come.

The first role is the smallest: a relay between two prototype block producers.

```text
  Node1 (prototype, pool1) ── Node2 (relay under test) ── Node3 (prototype, pool3)
```

This is [proto-devnet](../proto-devnet) with `TOPOLOGY=line` and its middle node swapped. The producers are only connected through the relay, so everything that Node3 learns from Node1, and the other way around, was relayed by the node under test: blocks, transactions, endorser block announcements and votes.

## Voting, but never certifying

In proto-devnet's genesis three pools hold a third of the stake each, all are on the Leios committee, and the quorum is 0.75. The relay runs without pool2's keys, so its seat never votes. The two producers vote with two thirds of the stake, so votes flow but no endorser block is ever certified.

That keeps certificates off the chain while the production node cannot yet validate them. The `Acceptance` process tallies per node the endorser blocks announced, votes cast, `MsgLeiosVotes` received and endorser blocks certified. It fails as soon as anything gets certified, since that means the setup is broken.

## Feature parity

With the relay under test in place, these are the milestones, each visible in the `Acceptance` tally, Grafana, and the visualizer:

1. **Praos relaying**: the relay follows the chain and Node3's mempool fills, although only Node1 receives transactions.
2. **Announcement relaying**: each producer receives the other's endorser block announcements.
3. **Vote relaying**: each producer receives the other's votes for its own endorser blocks.
4. **Endorser block diffusion**: each producer fetches, validates and votes for the other's endorser blocks too, so votes cast double.
5. **Certification**: bring pool2 back as a voter and the network certifies through the production relay.

Later roles replace a producer with a production node, and then all of them.

By default the relay is the prototype node too. That run is the reference: it reaches milestone 4, and shows what the production relay has to match. It also shows that the prototype sends every vote back to the peer it came from, so each producer receives its own votes as well.

## Getting started

Run the reference with nix:

```shell
nix run github:input-output-hk/ouroboros-leios#demo-acceptance
```

To run the acceptance, point the relay at a `cardano-node` built against ouroboros-consensus `main`:

```shell
cd demo/acceptance
nix develop ../..#dev-demo-acceptance
RELAY_CARDANO_NODE=/path/to/production/cardano-node ./run.sh
```

Every proto-devnet option applies, for example `TC=0` to run without network namespaces and traffic control, or `XRAY=0` without the observability stack. `CARDANO_NODE_1` and `CARDANO_NODE_3` swap the producers.

To reset, remove the working directory:

```shell
chmod a+w -R tmp-acceptance && rm -rf tmp-acceptance
```

## Observing

- The `Acceptance` process prints the tally every ten seconds.
- Grafana at <http://localhost:3000> has proto-devnet's dashboards; the voting dashboard shows votes per producer.
- The [visualizer](../../ui)'s live `Demo Prototype Devnet` scenario shows the network; run it with `nix run .#ui-live` while the demo is up. Messages are animated from the producers' traces too, so the relay's links show traffic even where the production relay traces differently from the prototype.
