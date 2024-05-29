## 2024-05-29

### Visualising node behaviour

* Added a simple web server rendering the throughput of IBs and EBs to basic Leios simulation
  * It uses `Tracer` interface to have the simulation code send JSON-formatted traces that are retrieved by the server and exposed through a WS interface.
  * The UI connects to the WS, retrieves the data and plots in on a live graph

> ![NOTE]
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
