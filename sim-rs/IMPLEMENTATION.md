# Overall Architecture

The simulation is made of two crates. The sim-core crate actually runs the simulation, producing an in-memory stream of events. The sim-cli crate is mostly a simple CLI wrapper around sim-core; it lightly processes that event stream, logs interesting stats about it, and saves it to disk.  The sim uses tokio as an asynchronous runtime, and sim-cli runs it as a multithreaded program.

The primary actors of the simulation are "nodes". A node can be either a stake pool or a relay; relays are simply stake pools without any stake. Nodes communicate to each other by sending messages over a simulated network, which is also implemented as an actor.

The simulation is not fully deterministic: if two events can happen at the same time, either could be simulated "first". For instance, if a node learned about a new transaction from three peers at the same instant, it could choose to request that transaction from any of the three.

## Clock

The simulation uses a virtual clock decoupled from real time. Time passes at the same rate for every node (no actor is ever "ahead" of any others). When an actor has finished simulating the current moment, it can either `wait_until` a specific timestamp or `wait_forever`, and the clock only advances once all actors are waiting for time to pass. Actors can also stop waiting at any time.

The clock has configurable timestamp resolution, which is implemented by rounding up the timestamp passed to `wait_until`. This improves performance by causing more events to happen simultaneously, letting the sim take advantage of multiple cores.

## Network

Nodes communicate with each other over the network through explicitly-configured connections. A connection has latency (in ms) and bandwidth (in bytes per second). Every connection tracks bandwidth independently, so a node with 10 connections at 1MiB/s effectively has 10MiB/s of bandwidth. We also track bandwidth independently in each direction; if there's a 1MiB/s connection between A and B, A can send 1MiB/s to B while B sends 1MiB/s to A.

Every message is tagged with a mini-protocol; within a connection, bandwidth is split equally between all active mini-protocols. If there's a 1MiB/s connection between A and B, and A is sending a transaction and an input block to B, 512MiB/s is dedicated to the TX and 512MiB/s is dedicated to the IB (and no bandwidth is dedicated to EBs/votes/RBs). Messages with the same mini-protocol are sent serially, messages with different mini-protocols are sent in parallel.
The network is implemented as an actor, running on its own dedicated task and communicating with other actors through message passing.

We do not need to explicitly support pipelining, since mini-protocols are not implemented as state machines and network activity is fire-and-forget.

When a message is sent over a connection, the delay is computed by applying the bandwidth first, followed by the latency. On a connection with 10MiB/s of bandwidth and 20ms latency, a 1 MiB message will be delayed by 100ms due to bandwidth, plus 20ms due to latency. Multiple messages can be in flight over a connection at a time; all bandwidth will be applied to the first message in the queue until it has been fully "sent".


# Protocol implementation

## Mini-Protocols

Every mini-protocol uses roughly the same implementation. To propagate some resource X throughout the network, there are three messages involved:

1. `AnnounceX`
2. `RequestX`
3. `X`

When a node first receives or creates X, it sends an `AnnounceX` message to its consumers. When a node receives an `AnnounceX` message, it may decide whether or not to request the resource; if it does, it sends a `RequestX` message in response. When a node receives a `RequestX` message, it responds to the sender with an `X` message. This is not technically a pull-based protocol, but it has similar performance properties to one.

The only resources which break this announce-request-send pattern are input blocks. Input block headers and bodies are propagated separately. More information about this is in the "Input Blocks" section of the Leios variant document.

The `relay-strategy` configuration option controls what a node does when two producers have both announced the same resource. If this option is `"request-from-first"`, the node will only request the resource from the first producer to announce it. If the option is `"request-from-all"`, the node will request the resource from every peer which announces it until one of them has successfully delivered it. Most simulations have been run with this set to `"request-from-first"`.

## Transactions

Each transaction has
* A unique integer id
* A size in bytes
* A randomly-assigned shard
* An "input_id", representing a single TXO which the transaction consumed
* An "overcollateralization factor", representing how much extra collateral the TX includes (only used by Leios)

All transactions are "produced" by a single actor called the `TransactionProducer`. This actor samples from an exponential distribution to control how long to wait between producing new transactions, and a log-normal distribution to control the size in bytes (both distributions are configurable). Each new transaction is sent to a randomly selected node, which then "generates" it and propagates it to its peers.

Note that in the rust sim, transactions travel in the same direction as all other blocks (from producer to consumer). All topologies used to test are fully connected, so this hasn’t resulted in any lost transactions.

Transaction production can be disabled by setting `simulate_transactions` to false in config. When transactions are disabled, the `TransactionProducer` will do nothing, and nodes will not randomly generate or propagate transactions. The simulation will produce "fake" transactions to fill any IBs/EBs/RBs as needed, so that these blocks still have realistic sizes.

## Variants
There are three implementations of Leios in this simulation. Similar variants tend to use the same implementations.

 * [Leios](./implementations/CLASSIC_LEIOS.md)
   * Short Leios: IBs contain transactions, EBs reference IBs
   * "Full" Leios: IBs contain (or reference) transactions, EBs reference IBs and older EBs
 * [Stracciatella](./implementations/STRACCIATELLA.md): EBs reference transactions, as well as other EBs
 * [Linear](./implementations/LINEAR_LEIOS.md): EBs contain (or reference) transactions, and do not reference other EBs. New EBs are produced whenever new blocks are produced.
