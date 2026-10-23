# P2P Payload Diffusion Simulator

Emulates a pull-based P2P diffusion protocol over a realistic network using Mininet with Linux tc traffic shaping and a per-link middlebox architecture.
The protocol disseminates large payloads (up to 12 MB, thousands of components) across a mesh of nodes with heterogeneous link characteristics, and is driven by a pluggable Python scheduler.

## Quick start

Run a single simulation and generate plots:

    SCHEDULER=FetchScheduler \
      bash run_and_plot.sh inputfiles/topo-8-1.json \
                           inputfiles/schedule-12MB-11-20s-apart-coinj8.json \
                           results/my-run --duration 50

This builds the Docker image, merges the topology and schedule into a single `input.json`, runs the simulation inside a privileged Mininet container, and produces goodput plots and a topology diagram in the results directory.

`--duration 0` skips the simulation and only regenerates the metadata + `topology.png` (handy for iterating on the topology-diagram rendering).

`SCHEDULER` selects the Python module loaded by the C node via a cached handle. Options:

- `FetchScheduler` — BDP-aware scheduler with pipeline-depth calibration, rebalancing, and threshold-based hedging. The primary subject of the design docs.
- `OnePeerScheduler` — request the whole payload from the first peer that offered. Minimal bandwidth, worst tail latency.
- `FullHedgeScheduler` — request every chunk from every offering peer, cancelling duplicates on delivery. Maximal tail protection, highest bandwidth waste.

See `ANALYSIS.md` for a head-to-head comparison on `topo-8-1`.

Run a batch of N simulations (sequential, parallel plotting):

    bash batch_run.sh inputfiles/topo-8-1.json inputfiles/schedule-12MB-12345.json my-experiment 20

Outputs per run (in the results directory):

- `input.json` — merged topology + schedule used for this run
- `t0.txt` — shared epoch timestamp (x-axis origin for plots)
- `topology.png` — annotated network topology diagram with middleboxes and per-hop qdiscs
- `edge_utilization_mininet.html` — per-edge goodput plots
- `nodeN.stderr` — per-node application-level logs
- `nodeN.stdout` — binary write traces
- `nodeN.pcap` — per-node packet captures

## Input files

See `input.json.md` for the full schema. A simulation is a merge of two files:

- A topology file (`inputfiles/topo-*.json`) — `edges`, `nic_bw_mbit`, `tuned_initcwnd`, `node_nicknames`, `default_duration`.
- A schedule file (`inputfiles/schedule-*.json`) — payloads with `time`/`node` (scalar or equal-length arrays for co-injection), `nickname`, `components`.

`run_and_plot.sh` merges them with `jq -s '.[0] + {schedule: .[1]}'` and pipes the result to the container via stdin.

## Available topologies

**topo-8-1** — 8 source nodes, each with a distinct `bw_mbit` / `delay` / `jitter` / `loss_gemodel` link to a single Sink.
Designed to stress tail-latency scenarios; used as the reference comparison in `ANALYSIS.md`.

**topo-small-world** — 7 nodes in a geographically-distributed mesh (Azure inter-region latencies as inspiration).
Bidirectional pulls on all edges; exercises mesh-diffusion behaviour.

**topo-1-10-1** — hub-spoke-hub layout (kept for historical reference).
Mostly superseded by `topo-8-1` + co-injection schedules, which can reproduce the same staggered-arrival dynamics without the extra layer.

## Network model

### Middlebox per edge

Each edge `(A, B)` is materialised as a dedicated Mininet host `mbN` placed between A and B:

    host A  ──[netem]──  mbN  ──[htb + fq_codel]──  host B

- `netem` (delay + jitter + Gilbert-Elliott loss) lives on the host-side veth. It models propagation delay and wire loss.
- `htb` (per-link rate) + `fq_codel` (AQM) live on the middlebox's egress toward the far host. This is the real bottleneck queue; fq_codel drops when its queue latency exceeds 5 ms, giving cubic a timely loss signal.

This separation is deliberate. Putting all tc chains on host egress interfaces (no middlebox) collapses into a per-peer HTB class structure that forces `netem`'s big packet buffer *above* the AQM, turning it into the effective bottleneck queue and defeating fq_codel.
See NOTES.md's "Middlebox-based network emulation" section for the full reasoning.

Each host has identity IP `10.0.0.<node_id>/32` on `lo`; each veth pair gets a `/24` subnet; routes and IP forwarding wire everything together so the app layer still addresses peers by `10.0.0.<id>`.

### TCP tuning

- Nodes listed in `tuned_initcwnd` get `initcwnd=200 initrwnd=200` on their per-peer routes (skip slow-start).
- `tcp_rmem[2]` and `tcp_wmem[2]` are raised to 16 MB per host so autotune has headroom on high-BDP links.
- We deliberately do **not** call `setsockopt(SO_RCVBUF)` — that disables autotune and gets clamped to the un-raisable `net.core.rmem_max` (see `NOTES.md` and `memory/project_tcp_rcvbuf_trap.md`).

### TCP_NOTSENT_LOWAT and two-tier write queues

Each socket sets `TCP_NOTSENT_LOWAT` (512 KB) to bound the unsent portion of the kernel send buffer.
The C node keeps two write queues per peer: high-priority (offers, manifests, cancels) and low-priority (response data).
This ensures protocol control messages (particularly MSG_CANCEL_CHUNK) aren't stuck behind bulk chunk data.
Additionally, `flush_queue` polls `ioctl(SIOCOUTQNSD)` between writes and yields once notsent hits the threshold — the kernel's epoll-gating doesn't apply to our tight `write()` loop, so we enforce the cap ourselves.

### MSG_CANCEL_CHUNK and queue purging

When a chunk is delivered from one peer, the scheduler emits MSG_CANCEL_CHUNK for any remaining peers that are also requested for that chunk.
Receivers purge the matching entry from their low-priority queue if it hasn't been handed to the kernel yet.
Anything already written to the kernel is committed and will transmit regardless.

## Goodput measurement

The C node emits a binary write trace to stdout (18-byte records: wallclock, dst_ip, dst_port, bytes_written) taken before each `write()` syscall.
Receiver-side pcap captures the same packets after the tc stack. The difference is true end-to-end delay including htb queuing, netem delay, and fq_codel AQM.

`plot_mininet.py` computes per-packet goodput with a write-trace-aware dt cap (to avoid inflating rates across transfer gaps) plus a 0.1 s binned curve for smoothing.
Receiver packets are deduplicated by TCP sequence number — it's goodput, not throughput.

## File overview

| File | Purpose |
|------|---------|
| `node.c`, `node.h` | C infrastructure: networking, epoll loop, schedule loading, write trace |
| `diffusion.c` | Protocol: OFFER/REQUEST/RESPONSE/CANCEL message handling |
| `scheduler_bridge.c`, `scheduler_bridge.h` | C ↔ Python bridge for the scheduler plugin |
| `FetchScheduler.py` | BDP-aware scheduler (main policy) |
| `OnePeerScheduler.py` | Minimal baseline: request everything from the first offerer |
| `FullHedgeScheduler.py` | Maximal baseline: request everything from everyone, cancel on delivery |
| `topo_config.py` | Parse `input.json` topology |
| `mininet_topo.py` | Mininet runner: build hosts + middleboxes, apply tc, launch nodes |
| `plot_mininet.py` | Per-edge goodput HTML (interactive scatter/binned toggle) |
| `plot_topology.py` | Graphviz topology diagram with per-hop qdisc annotations |
| `run_and_plot.sh` | Single run: merge inputs, simulate, plot |
| `batch_run.sh` | N sequential runs with parallel plotting |
| `Dockerfile.mininet` | Container image with Mininet, tc tools, iperf3, and the C node |
| `DESIGN.md` | Fetch-strategy design rationale |
| `ANALYSIS.md` | Head-to-head comparison of the three schedulers |
| `NOTES.md` | Technical notes on TCP tuning, timestamp alignment, middlebox architecture |
| `input.json.md` | Full `input.json` schema |
| `bdp_demo/` | Standalone demo of the challenges of receiver-side BDP measurement |
