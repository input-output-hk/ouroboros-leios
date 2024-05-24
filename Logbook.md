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
