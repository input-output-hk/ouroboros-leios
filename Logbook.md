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
