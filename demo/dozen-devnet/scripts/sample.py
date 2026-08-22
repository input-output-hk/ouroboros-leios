#!/usr/bin/env python3
"""Sample every node's Prometheus endpoint into a TSV, one row per interval.

    scripts/sample.py > results/<run>/sampler.tsv

Everything here is a chain- or node-level metric read straight off the node. Two
kinds of column, and the difference matters when reading a run:

  chain-wide   `cumulativeTxBytes` is read from the ledger state at the tip, so
               every producer reports the same value. This is the ONLY
               trustworthy source for on-chain throughput.
  node-local   forge counters, mempool depth, txsAccepted. A node-local counter
               is not a chain quantity — `txsProcessedNum` was read as confirmed
               throughput once and understated it by a third, because a tx
               confirmed in an EB the node never fetched is never counted.

The forge counters are summed across the three producers, which is what makes
them a network figure: each EB is forged once, by one producer.

Phase is the number of running generators, discovered from process-compose, so
starting TxFirehose2 mid-run labels the rows that follow without any bookkeeping
here.
"""

import argparse
import json
import sys
import time
import urllib.error
import urllib.request

BPS = ["bp1", "bp2", "bp3"]
RELAYS = [f"relay{g}{n}" for g in (1, 2, 3) for n in (1, 2, 3)]
NODES = BPS + RELAYS

METRICS_PORT = 12798
PC_PORT = 8080

# The Nth node in NODES gets IP_PREFIX(IP_OFFSET + N) — mirrors node_ip() in run.sh.
IP_PREFIX = "172.29.0."
IP_OFFSET = 10

# Scalars we take as-is.
GAUGES = {
    "slot": "cardano_node_metrics_slotNum_int",
    "blocks": "cardano_node_metrics_blockNum_int",
    "cumTxBytes": "cardano_node_metrics_cumulativeTxBytes_int",
}
# Per-node gauges, one column per node.
PER_NODE_GAUGES = {
    "mp": "cardano_node_metrics_txsInMempool_int",
    "mpB": "cardano_node_metrics_mempoolBytes_int",
}
# Per-node counters, reported as a per-second rate against the previous sample.
PER_NODE_RATES = {"in": "cardano_node_metrics_txSubmission_txsAccepted_int"}
# Forge counters, summed over the three producers. These are the ones this node
# build actually exports — the Forge_ranking_*/Forge_endorser_* families appear
# in the shared dashboards but not in this node's metrics, so EB fill and the
# chain's bytes-per-tx come from digest.py's log extraction instead.
# forged vs adopted is the interesting pair: a gap means a block was produced and
# then lost, which is what a slow forge loop causes.
FORGE = {
    "forged": "cardano_node_metrics_Forge_forged_counter",
    "adopted": "cardano_node_metrics_Forge_adopted_counter",
    "didntAdopt": "cardano_node_metrics_Forge_didnt_adopt_counter",
    "leader": "cardano_node_metrics_Forge_node_is_leader_counter",
}


def node_ip(name):
    return f"{IP_PREFIX}{IP_OFFSET + NODES.index(name) + 1}"


def scrape(name, timeout=3):
    """Prometheus text format -> {metric: float}. Empty dict if the node is down."""
    url = f"http://{node_ip(name)}:{METRICS_PORT}/metrics"
    try:
        with urllib.request.urlopen(url, timeout=timeout) as response:
            body = response.read().decode()
    except (urllib.error.URLError, OSError):
        return {}
    out = {}
    for line in body.splitlines():
        if not line or line.startswith("#"):
            continue
        key, _, value = line.partition(" ")
        try:
            out[key.split("{")[0]] = float(value)
        except ValueError:
            continue
    return out


def generators_running(timeout=2):
    """How many tx-firehose processes are up — the run's phase."""
    try:
        url = f"http://localhost:{PC_PORT}/processes"
        with urllib.request.urlopen(url, timeout=timeout) as response:
            data = json.loads(response.read().decode())
    except (urllib.error.URLError, OSError, ValueError):
        return ""
    procs = data.get("data", data) if isinstance(data, dict) else data
    if not isinstance(procs, list):
        return ""
    return sum(
        1
        for p in procs
        if isinstance(p, dict)
        and str(p.get("name", "")).startswith("TxFirehose")
        and str(p.get("status", "")).lower() in ("running", "ready")
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--interval", type=float, default=10.0, help="seconds between samples")
    parser.add_argument("--count", type=int, default=0, help="samples to take (0 = until killed)")
    args = parser.parse_args()

    columns = (
        ["phase", "t", "slot", "blocks", "cumTxBytes", "confBps"]
        + list(FORGE)
        + ["mpBytesPerTx"]
        + [f"mp_{n}" for n in NODES]
        + [f"mpB_{n}" for n in NODES]
        + [f"in_{n}" for n in NODES]
    )
    print("\t".join(columns), flush=True)

    start = time.time()
    previous = {}
    previous_bytes = None
    previous_time = None

    taken = 0
    while args.count == 0 or taken < args.count:
        now = time.time()
        samples = {n: scrape(n) for n in NODES}
        row = {"phase": generators_running(), "t": f"{now - start:.0f}"}

        # Chain-wide gauges: take them from any producer that answered. They agree
        # by construction, so the first non-empty reading is as good as a vote.
        for label, metric in GAUGES.items():
            for n in BPS:
                if metric in samples[n]:
                    row[label] = f"{samples[n][metric]:.0f}"
                    break

        # On-chain byte rate, differenced against the previous sample.
        current_bytes = next((samples[n].get(GAUGES["cumTxBytes"]) for n in BPS if samples[n].get(GAUGES["cumTxBytes"])), None)
        if current_bytes is not None and previous_bytes is not None and now > previous_time:
            row["confBps"] = f"{(current_bytes - previous_bytes) / (now - previous_time):.0f}"
        previous_bytes, previous_time = current_bytes or previous_bytes, now

        # Forge counters, summed over producers — each block is forged once.
        totals = {}
        for label, metric in FORGE.items():
            values = [samples[n][metric] for n in BPS if metric in samples[n]]
            if values:
                totals[label] = sum(values)
                row[label] = f"{sum(values):.0f}"
        for prefix, metric in PER_NODE_GAUGES.items():
            for n in NODES:
                if metric in samples[n]:
                    row[f"{prefix}_{n}"] = f"{samples[n][metric]:.0f}"
        # What the mempool charges per transaction, averaged over the entry relay.
        # Compare against the 228 B on the wire: the mempool, the wire and the
        # ledger do not agree, and every tx/s figure depends on which one is used.
        depth = samples["relay11"].get(PER_NODE_GAUGES["mp"])
        depth_bytes = samples["relay11"].get(PER_NODE_GAUGES["mpB"])
        if depth and depth_bytes:
            row["mpBytesPerTx"] = f"{depth_bytes / depth:.1f}"

        for prefix, metric in PER_NODE_RATES.items():
            for n in NODES:
                current = samples[n].get(metric)
                if current is None:
                    continue
                was = previous.get((prefix, n))
                if was is not None and now > was[1]:
                    row[f"{prefix}_{n}"] = f"{(current - was[0]) / (now - was[1]):.0f}"
                previous[(prefix, n)] = (current, now)

        print("\t".join(str(row.get(c, "")) for c in columns), flush=True)
        taken += 1
        # Drift-free: aim at the next multiple of interval rather than sleeping a
        # fixed amount after however long the scrape took.
        time.sleep(max(0.0, start + taken * args.interval - time.time()))


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(0)
