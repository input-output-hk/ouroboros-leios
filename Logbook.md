## 2024-09-20

### Team meeting

- Introductions and roles
    - Excellent balance of Agda, Haskell, and Rust skills
- Reviewed administrative informoration
    - PI7 Jira tickets, mirrored at [#16](https://github.com/input-output-hk/ouroboros-leios/issues/16), [#17](https://github.com/input-output-hk/ouroboros-leios/issues/17), [#18](https://github.com/input-output-hk/ouroboros-leios/issues/18)
    - Nominal objectives, tasks, and deliverables for next 12 months
- Work agreement
    - Write down “everything” in a “research journal”
        - what we do
        - why we do it
        - what are the expected results vs. actual results.
    - Regular (at least weekly) technical review of all work done by everyone
    - Show & tell sessions
    - Communicate with the stakeholders (including community) on a regular basis
    - Experimenting, pivoting, and dead-ends provide valuable learnings and should be documented in logbook
    - Processes and workflows can emerge from our needs, and do not have to match typical production enviroments
        - However, QA and checking each others' work is important
    - Ensure all results are “easily” reproducible by the community
    - Arnaud will pair with engineering staff each week in October
    - Technical report each quarter -- the next will be in December
    - CIP at conclusion of innovation workstream
- Project resources listed at [discussion #15](https://github.com/input-output-hk/ouroboros-leios/discussions/15)
- Open discussion
    - Leios flavors
        - Blob, short, simplified, and full
        - All flavors have the same security guarantees
        - Blob Leios does not deal with Cardano transactions
        - Full Leios adds robust throughput even in the face of performance issues in base protocol
    - Details of interaction with ledger
        - Fairness for fees
        - Wastage (i.e., duplicate or conflicting transactions)
        - Time-dependent smart contracts
    - Demo of initial DeltaQ rust implementation by Roland
    - Brian will coordinate with David about contracts and with Hans about tweeting
- Communication and collaboration
    - Use slack channel for admistrative and scheduling
    - Use github [discussions](https://github.com/input-output-hk/ouroboros-leios/discussions) or [pull requests](https://github.com/input-output-hk/ouroboros-leios/pulls)
        - When relevant, summarize discussion results or PR comments in [this logbook](./Logbook.md)
    - Put experimental code and work in progress on the main branch of [this repository](./)
        - Avoid long-lived branches
        - If warranted, code can later be separated into a new repository via `git subtree`
        - Mostly keep main branch passing the CI, but short-lived exceptions are okay
        - Describe new work and findings in [this logbook](./Logbook.md)
    - Approximately three working meetings per week
        - Each meeting (or slack) will settle the topic for the next meeting
- Next steps
    - Meetings next week approximately at 1400 UTC
        - Duncan will present on existing ouroboros network
        - Two meetings to discuss, brainstorm, and plan network simulations
    - Future meetings
        - Duncan will present on ouroboros consensus protocol
        - Duncan will present on praos lessons learned
        - Arnaud, Yves, or Brian will present on peras lessons learned
        - Andre will present on formalization lessons learned
        - Additional protocol and formalization meetings
        - At some point we'll meet with PNSol about DeltaQ collaboration
    - Possible in-person meeting mid December or January?
    - Work focus
        - Roland and Yves will collaborate on DeltaQ
        - Everyone should familiarize themselves with the [simulation/](simulation/) and [leios-sim/](leios-sim/) code
            - Live version of `leios-sim` at https://leios-simulation.cardano-scaling.org/index.html
            - Run `simulation` locally via [instructions below](#running-ouroborous-net-viz-in-the-browser)

## 2024-07-26

### Running `ouroborous-net-viz` in the browser

It is relatively straightforward to run GTK applications like `ouroborous-net-viz` in a web browser. Here is one recipe.

Start a broadway daemon:

```console
$ nix develop

$ broadwayd --port 8282 :5
Listening on /run/user/120065/broadway6.socket
```

In another terminal window, run the visualizer using the broadway backend, ignoring the messages:

```console
$ GDK_BACKEND=broadway BROADWAY_DISPLAY=:5 nix run .#ouroboros-net-vis -- p2p-1
/nix/store/aw2fw9ag10wr9pf0qk4nk5sxi0q0bn56-glibc-2.37-8/lib/libc.so.6: version `GLIBC_2.38' not found (required by /nix/store/rgafsh9w6yrklqbmz6gb0cvdy10ja9mv-libxfce4util-4.18.2/lib/libxfce4util.so.7)
Failed to load module: /nix/store/s9ah4nlrxxbmzzzwqp3rf43cyr0cwnv7-xfconf-4.18.3/lib/gio/modules/libxfconfgsettingsbackend.so
/nix/store/aw2fw9ag10wr9pf0qk4nk5sxi0q0bn56-glibc-2.37-8/lib/libc.so.6: version `GLIBC_2.38' not found (required by /nix/store/nf5mmvq3cayv4z3jcnhapiqjzh3brcd2-gvfs-1.54.1/lib/gio/modules/libgvfsdbus.so)
Failed to load module: /nix/store/nf5mmvq3cayv4z3jcnhapiqjzh3brcd2-gvfs-1.54.1/lib/gio/modules/libgvfsdbus.so
```

Visit `localhost:8282` in the browser.

Here is a video: [![image](https://github.com/user-attachments/assets/88af2794-148a-49d8-8164-ba8790b6b3de)](https://vimeo.com/990683045/74a915afd2?share=copy)

We'd have to add session management and UI components to make this generally useful. Alternatively, it could be packaged as a Docker image.

### Dependency upgrades, Nix, and CI

- We upgraded [ouroboros-net-sim](./simulation/) to use the latest `io-sim`, `io-classes`, and `si-timers` with very few changes to the source code and with the addition of a new `TimeCompat` module.
- A nix shell and derivations was also added for the targets in the project.
- Builds and tests were added to the CI

## 2024-07-19

### Comments on `leios-sim`

Here are a few comments by @bwbush about the `leios-sim` package:

1. I think we should bite the bullet and add a `MonadRandom` instance to io-classes. Explicitly passing RNGs around makes the code harder to read and refactor.
2. Even without that, when the code becomes more complicated, we should consider using a monad transformer stack that includes a `MonadRandom` instance.
3. Along the same lines, we might want to minimize or hide the use of `TVars` and offload that to some State types so functions can live in `MonadState`. Once again, this will let the implementation functions read more abstractly and make later refactoring easier as the implementation evolves.
4. The unit conversion that we have to do (e.g., seconds to milliseconds) have always bothered me because it would be easy to make a mistake. Having put the unit in `bitsPerSecond` helps somewhat.
    1. Use one of the time types (or even `Data.Fixed`) instead of a custom `Microseconds` would help somewhat.
    2. The typechecked dimension packages like [units](https://hackage.haskell.org/package/units) feels like overkill, but maybe they are worth it. My understanding is that these dimensional analysis packages have no runtime overhead: they'd prevent unit errors at compile time.
5. The use of newtype wrappers was good. We could automatically derive Num instances for those, but that would decrease safety at the expense of increasing readability. (Hence, my comment on units.) I'm not sure.
6. I think the design does a reasonable job of separating the transport aspects from the logic aspects. We'll probably need a more sophisticated network representations, maybe event separating the network interface from the network itself.
    1. BTW, I think a big challenge for leios prototyping will be accurately representing network contention between the different leios roles, the base protocol, and the memory pool in high-throughput situations. Even without an adversary, I'm concerned that some parts of the implementation might starve others.
7. So far as I can tell, the simulation reasonably approximates a simplified Leios.
8. The complexity and verbosity are okay at this point because it's laying necessary groundwork (subject to refactoring) for the next level of fidelity: it highlights areas of complexity and opportunities for modularization. I think the Leios simulation will need many cycles of refactoring in order to control complexity and leverage modularity.

### Document simulation

Added some documentation to the Leios simulator:

* Added _tooltips_ to document the various parameters available
* Added readonly fields computing various aggregates from the simulation's data: Throughput, latency to inclusion in EB, dropped IB rate
* Added a [comment](https://github.com/input-output-hk/ouroboros-leios/issues/7#issuecomment-2236521300) on the simulator issue as I got perplexed with the throughput computation's result: I might be doing something wrong and not computing what I think I am computing as the results are inconsistent. I think this comes from the fact we are simulation 2 nodes so the throughput aggregates the 2 nodes' and should be assigned individually to each one, perhaps more as a distribution?

## 2024-07-11

### Deploying simulation in the "cloud"

Started working on simnulation deployment on AWS.
  * Found this repository for setting up ECS which sounds the most promising option: https://github.com/ajimbong/terraform-ecs-cicd-project.
  * This article contains the GHA workflow part: https://ajimbong.medium.com/deploy-a-docker-container-to-amazon-ecs-using-github-actions-fd50261b8e03
  * Following tutorial here: https://developer.hashicorp.com/terraform/tutorials/aws-get-started/aws-build
  * installing AWS command-line from https://docs.aws.amazon.com/cli/latest/userguide/getting-started-install.html

Created service account `leios-build` with power user rights, and generated access keys. TODO: reduce rights to the strict minimum

Managed to deploy ECS cluster with defined service, but there's no EC2 instance container attached so it cannot run :( => use Fargate?

Managed to configure the ECS cluster, service, and task to run the image, but it now fails to download the manifest from ghcr.io which seems a permissions issue. I need to add the necessary configuration to the task/service?

need to configure a secret containing a PAT for pulling the manifest: https://docs.aws.amazon.com/AmazonECS/latest/developerguide/task_definition_parameters.html#container_definition_repositoryCredentials

I gave up trying to run on AWS, every solution I found is an insanely intricate maze of stupidly complicated solution which I don't care about as I only need to deploy a _single_ image without any data dependency attached.

I managed to get Gcloud run deployment working, mostly copy pasting what I did peras and fiddling with it.

* I reused same service account than Peras which is  a mistake -> should create a new service account with limited rights
* Needeed to add service account as an _owner_ of the domain in the google console (a manual task) in order to allow subdomain mapping
* Changed the server code to support defining its port from `PORT` environment variable which is provided by the deployment configuration

Allowing anyone to access the server proved annoying too: The folowing configuration works
```

resource "google_cloud_run_service_iam_member" "noauth" {
  location = google_cloud_run_v2_service.leios_server.location
  service  = google_cloud_run_v2_service.leios_server.name
  role     = "roles/run.invoker"
  member   = "allUsers"
}

```

but note that it does not have a `_v2_` tag! This was the mistake I made, I used a v2 iam_member with `name` proeprty which proved to be incorrect.
Invalid argument `2024-07-11'

### Weekly update

* initial design was geared toward optimal usage of bandwidth
  * => bandwidth is large, and it can accomodate spikes, so perhaps focus on something simpler?
  * developed a short pipeline which is much simpler
  * assumes 40% of bandwidth and needs to tolerate spikes (2.5x average throughput), provides same security, consume bandhwidth ~ throughput
  * seems ideal for pricing model based on volume

* could there be a use case for blob leios in the partner chain space?

## 2024-07-04

### Network pricing

Did some quick research on network pricing for a few major Cloud or VPS providers: https://docs.google.com/document/d/1JJJk4XPqmP61eNWYNfqL8FSbKAF9cWazKWFZP6tMGa0/edit

Comparison table in USD/mo for different outgoing data transfer volumes expressed as bytes/seconds and similar VMs (32GB RAM, 4+ Cores, 500GB+ SSD disk). The base cost of the VM is added to the network cost to yield total costs:

| Provider     | VM     | 50kB/s | 125kB/s | 250kB/s |
|--------------|--------|--------|---------|---------|
| DigitalOcean | $188   | $188   | $188    | $188    |
| Google Cloud | $200   | $213.6 | $234    | $268    |
| AWS          | $150 ? | $161.1 | $177.9  | $205.8  |
| Azure        | $175   | $186   | $202    | $230    |
| OVH          | $70    | $70    | $70     | $70     |
| Hetzner      | $32    | $32    | $32     | $32     |

Notes:

* the AWS cost is quite hard to estimate up-front, obviously on purpose. The $150 base price is a rough average of various instances options in the target range
* Google, AWS and Azure prices are based on 100% uptime and at least 1-year reservation for discounts

### Weekly meeting

* There's a simplified pipeline being worked on from Matthias -> shortens pipeline assuming we don't want to go above 0.4 Capacity
  * GP to share draft once available
* what about Blob leios?
  * Not much progress, we want to have a working simulation/PoC to be able to discuss over some concrete numbers with potential users
* there's a research stream started on incentives for storage
  * need to check with realistic cost models
  * Also need to take into account both rate and volume (typically for network usage in DCs, both are capped but one pays a linear fee for the later)
* SNARKs research
  * block producer generates a proof that other nodes can be verified
  * current: All voters verify the IBs => nr of voters is large so almost everyone is verifying
  * future: create proofs from IB producers that the IB is correct wrt ledger rule (mostly stage 2, smart contracts)
  * related to midnights
  * just have the heavy stuff (smart contracts)
* Ricky's comments:
  * how to guarantee different tx end up in different IBs?
  * sharding seems easier to solve than increasing throughputs?
* Tx diffusion not very well suited for Leios ?
  * need more work on mempool and network protocol for TXs

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
