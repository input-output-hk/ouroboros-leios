# Prototype demo - November 2025

Slight improvement of the [October 2025 demonstration](../2025-10) using `tc` and better observability using Grafana et al. In summary the progress made during November 2025 on the Leios networking prototype is:

- The surprisingly-high latency observed in the October demo was explained and reined in.
- Key structured log events were added to the prototype.
- Observability/reporting/monitoring was improved.
- Packaging of the prerequisites for executing the demo was improved.

![Demo diagram](./demo-2025-11.excalidraw.svg)

> [!TIP]
> This is an excalidraw SVG with embedded scene so it can be loaded and edited in [https://excalidraw.com/].

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

## Running the Leios 202511 demo

Run the Leios X-Ray (Grafana based observability stack)

```shell
export LOG_PATH=".tmp-leios-202511-demo/*.log"
nix run github:input-output-hk/ouroboros-leios#x_ray
```

Run the Leios experiment with default configuration

```shell
nix run github:input-output-hk/ouroboros-leios#demo-2025-11
```

If you want to further configure the experiment set the following environment
variables:

```shell
CARDANO_NODE=cardano-node
IMMDB_SERVER=immdb-server
DATA_DIR=data
REF_SLOT=41
SECONDS_UNTIL_REF_SLOT=5
LEIOS_MANIFEST=manifest.json
ANALYSE_PY=analyse.py
PYTHON3=python
RATE_UP_TO_N0="100Mbps";
DELAY_UP_TO_N0="20ms";
RATE_N0_TO_UP="100Mbps";
DELAY_N0_TO_UP="20ms";
RATE_N0_TO_DOWN="100Mbps";
DELAY_N0_TO_DOWN="20ms";
RATE_DOWN_TO_N0="100Mbps";
```

To clean up just delete the working directories

```shell
rm -fr .tmp-leios-202511-demo
rm -fr .tmp-x-ray
```
