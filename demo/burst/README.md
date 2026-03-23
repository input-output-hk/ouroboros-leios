# Protocol burst demo

Culmination of former `2025-10` and `2025-11` demos into a single protocol burst scenario. See git history prior to `96472a81e48f527277b7cdbffca28f84982970df` for removed and merged demo descriptions.

The architecture of this demo is as follows and it works by having Praos and Leios traffic prepared, which is released by `Upstream` on a pre-determined schedule at a very unfortunate time such that lots of Leios traffic is pulled from `Node0` and `Downstream`.

![Demo diagram](./demo-burst.excalidraw.svg)

> [!TIP]
> This is an excalidraw SVG with embedded scene so it can be loaded and edited in [https://excalidraw.com/].

## Praos and Leios traffic

In this iteration of the demo, the data and traffic is very simple.

- The Praos data is a simple chain provided by the Performance&Tracing team.
- The mocked upstream peer serves each Praos block when the mocked wall-clock reaches the onset of their slots.
- The Leios data is ten 12.5 megabyte EBs.
  They use the minimal number of txs necessary in order to accumulate 12.5 megabytes in order to minimize the CPU&heap overhead of the patched-in Leios logic, since this iteration of the demo is primarily intended to focus on networking.
- The mocked upstream peer serves those EBs just prior to the onset of one of the Praos block's slot, akin to (relatively minor) ATK-LeiosProtocolBurst attack.
  Thus, the patched nodes are under significant Leios load when that Praos block begins diffusing.

## Upstream

The mocked upstream peer is a patched variant of `immdb-server`.

- It runs incomplete variants of LeiosNotify and LeiosFetch: just EBs and EB closures, nothing else (no EB announcements, no votes, no range requests).
- It serves the EBs present in the given `--leios-db`; it sends Leios notificaitons offering the data according to the given `--leios-schedule`.
  See the demo tool section above for how to generate those files.

## Node0

The patched node is the latest prototype of `cardano-node`. At first, this was a very basic implementation of the Leios fetch protocol only with little persistence. In the meantime, the prototype was expanded to cover to also produce real EBs and relay other information.

For this demo to work, it is important that:

- Node0 to not hold stake, otherwise it would produce EBs themselves and interfere measurements
- Not validate EB transactions as the mocked Leios traffic is just placeholder bytes

## Downstream

For simplicity, this is simply another instance of the patched node.
In the future, it could be comparatively lightweight and moreover could replay an arbitrary schedule of downstream requests, dual to the mocked upstream peer's arbitrary schedule of upstream notifications.

## Bufferbloat

The investigation into the unexpectedly high latency seen in October and related refinements to the prototype are apparent in the asynchronous conversation that took place in the comments on a [tracking Issue](https://github.com/IntersectMBO/ouroboros-consensus/issues/1756).

- The latency was due to a network phenomena called [bufferbloat](https://www.bufferbloat.net)
  In October, the bufferbloat arose directly from the naive use of [Toxiproxy](https://github.com/Shopify/toxiproxy) for the initial demo.
- As user-space mechanism, Toxiproxy cannot introduce latency/rate/etc in a way that will influence the kernel algorithms managing the TCP stream.
- [Linux Traffic Control](https://tldp.org/HOWTO/Traffic-Control-HOWTO/intro.html) is the approriate mechanism.
- An example of relevant commands for a more appropriate WAN (Wide Area Network) emulation can be found in [this GitHub comment](https://github.com/IntersectMBO/ouroboros-consensus/issues/1756#issuecomment-3587268042).
  - `htb rate 100mbt` limts the sender's bandwidth.
  - `fq_codel` paces the sender's traffic, adapting to any bottleneck between it and the recipient.
  - `netem delay` established the link latency of 20ms between `fq_codel` and the recipient.
- The Networking Team is now taking over this aspect of the setup for future Leios demos, refining//enriching the WAN emulation, preparing some testing on actual WANs (physically separated machines), and considering which mechniams ought to mitigate the risk of Leios-induced bufferbloat (perhaps as part of an ATK-LeiosProtocolProtocolBurst) increasing the latency of Praos traffic once Leios is deployed on mainnet.

## Improved Logging

Additional key events in both the mocked upstream peer and the node-under-test are now emitted as structured JSON, which the demo's analysis script processes.
Highlights include the following.

- The node reliably indicates when concludes it acquired the last of the txs it was missing from an EB.
  In particular, this event is raised then a MsgLeiosBlockTx arrives with all the txs that the node was missing from some EB.
  Even if the final tx were to arrive as part of a separate EB, this event would still be emitted for each EB that the MsgLeiosBlockTx completes.
- Both the node and upstream peer report when ChainSync's MsgRollForward, BlockFetch's MsgRequestRange and MsgBlock, and Leios's MsgLeiosBlockRequest, MsgLeiosBlock, MsgLeiosBlockTxsRequest, and MsgLeiosBlockTxs are sent and received.
  The demo's analysis script displays a table of when these messages were sent and received.
  This table very usefully indicates how much to alter the timings in the `demoSchedule.json` file in order to change which parts of the Praos traffic a particular EB's exchange overlaps with.
- A patch to `ouroboros-network` was introduced to allow two additional timings, which will are expected to help make subsequent visualizations of the message exchange more accurate.
  - When a mini protocol begins trying to enqueue a message in the mux, even if the mux is unable to accept that message immediately.
  - When the demux receives the last byte of some message, even if the mini protocol doesn't attempt to decode that message immediately.
- The `ss` tool is being used to sample socket statistics throughout the demo's execution, so that the TCP algorithm's state can be monitored.
  For example, the `rtt` and `notsent` fields are directly related to bufferbloat.

## Getting started

Run the demo with all dependencies automatically provided using nix:

```shell
nix run github:input-output-hk/ouroboros-leios#demo-burst
```

Or enter the `nix develop` shell (also available via `direnv allow`) and follow [without nix instructions](#without-nix).

### Without Nix

Install these prerequisites:

- `process-compose` for orchestrating the demo processes
- `cardano-node` patched with Leios support
- `immdb-server` for the upstream node (mock server)
- `leiosdemo202510` for generating Leios schedules (TODO: cleanup/rename)
- `ss_http_exporter` for socket statistics monitoring
- `sqlite3` for creating Leios databases
- `jq` for config modifications
- `python` with `pandas` and `matplotlib` for analysis

Ensure they are on your PATH, override if needed with something like:

```shell
export PATH=/path/to/cardano-node:/path/to/immdb-server:$PATH
```

Then run:

```shell
./run.sh
```

## Configuration

You can customize the demo by setting environment variables before running. See `run.sh` for available options and their defaults:

```shell
# Network simulation parameters
export RATE_UP_TO_N0="100Mbps"
export DELAY_UP_TO_N0="20ms"
export RATE_N0_TO_UP="100Mbps"
export DELAY_N0_TO_UP="20ms"
export RATE_N0_TO_DOWN="100Mbps"
export DELAY_N0_TO_DOWN="20ms"
export RATE_DOWN_TO_N0="100Mbps"
export DELAY_DOWN_TO_N0="20ms"

# Timing
export REF_SLOT=41
export SECONDS_UNTIL_REF_SLOT=5

# Working directory
export WORKING_DIR=my-experiment

./run.sh
```

To use locally built binaries, simply adjust your PATH:

```shell
export PATH=$(cd ~/code/iog/cardano-node; dirname $(cabal list-bin cardano-node)):$PATH
export PATH=$(cd ~/code/iog/ouroboros-consensus; dirname $(cabal list-bin immdb-server)):$PATH
./run.sh
```

## Observability with X-ray

Run the Leios X-Ray (Grafana based observability stack) in a separate terminal:

```shell
export LOG_PATH="tmp-demo-burst/*.log"
nix run github:input-output-hk/ouroboros-leios#x-ray
```

Access Grafana at <http://localhost:3000>

## Clean up

To reset the demo, simply remove the working directories:

```shell
rm -rf tmp-demo-burst
rm -rf tmp-x-ray
```
