#!/usr/bin/env python3
"""Extract a run's digest from its logs, so the logs can then be deleted.

A two-generator run writes 1.7 GB of node logs in twenty minutes, and twice a run
has filled the disk and taken all twelve nodes down mid-write. The numbers below
are what those logs are actually for; everything else in them is volume.

The gap distribution is the reason this exists rather than a Prometheus query: a
0.4 ms per-add latency is invisible to a 1 s scrape interval, so it cannot be
recovered after the fact.

    scripts/digest.py tmp-devnet > results/<run>/digest.md
"""

import collections
import datetime
import glob
import os
import re
import statistics
import sys

# The node writes trace JSON inside a process-compose envelope, so the fields we
# want are escaped. A regex over bytes is ~20x faster than json parsing here, and
# at gigabyte scale that is the difference between usable and not.
AT = re.compile(rb'\\"at\\":\\"([^\\]+)')
NUM_TXS = re.compile(rb'\\"numTxs\\":(\d+)')
NS = re.compile(rb'\\"ns\\":\\"([^\\]+)')


def stamp(raw):
    return datetime.datetime.fromisoformat(raw.decode().replace("Z", "")).timestamp()


def scan(path, marker, want_size=False):
    """Timestamps of lines containing `marker`, and their mempool sizes."""
    times, sizes = [], []
    with open(path, "rb") as handle:
        for line in handle:
            if marker not in line:
                continue
            at = AT.search(line)
            if at:
                times.append(stamp(at.group(1)))
            if want_size:
                num = NUM_TXS.search(line)
                if num:
                    sizes.append(int(num.group(1)))
    times.sort()
    return times, sizes


def quantiles(sorted_gaps):
    def at(fraction):
        return sorted_gaps[min(int(len(sorted_gaps) * fraction), len(sorted_gaps) - 1)]

    return at(0.5), at(0.99), sorted_gaps[-1]


def main(run_dir):
    print("# Run digest\n")
    print("Extracted from the node and generator logs, which were then discarded.")
    print("`sampler.tsv` and `provenance.txt` sit alongside.\n")

    print("## Mempool add path, per node\n")
    print("| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for path in sorted(glob.glob(os.path.join(run_dir, "*", "node.log"))):
        name = os.path.basename(os.path.dirname(path))
        times, sizes = scan(path, b"Mempool.AddedTx", want_size=True)
        if len(times) < 3:
            continue
        span = times[-1] - times[0]
        gaps = sorted(b - a for a, b in zip(times, times[1:]))
        p50, p99, worst = quantiles(gaps)
        # Anything over half a second is a stall rather than scheduling noise.
        stalled = sum(g for g in gaps if g > 0.5)
        print(
            f"| {name} | {len(times)} | {len(times)/span:.1f} | {p50*1000:.1f} ms | "
            f"{p99*1000:.0f} ms | {worst:.1f} s | {100*stalled/span:.0f}% | "
            f"{max(sizes) if sizes else 0} |"
        )

    print("\n## Generators\n")
    print("| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap |")
    print("| --- | --- | --- | --- | --- | --- |")
    quiet_deaths = []
    for path in sorted(glob.glob(os.path.join(run_dir, "tx-firehose*.log"))):
        name = os.path.basename(path)
        times, _ = scan(path, b"Submit.Success")
        if len(times) < 3:
            continue
        span = times[-1] - times[0]
        per_second = collections.Counter(int(t) for t in times)
        rates = sorted(per_second.values())
        gaps = sorted(b - a for a, b in zip(times, times[1:]))
        zero = int(span) + 1 - len(per_second)
        print(
            f"| {name} | {len(times)} | {len(times)/span:.1f} | "
            f"{rates[len(rates)//2]} | {100*zero/(int(span)+1):.0f}% | {gaps[-1]:.1f} s |"
        )
        # A generator that dies quietly looks exactly like "the load did not help",
        # so always surface whatever else it logged.
        other = collections.Counter()
        with open(path, "rb") as handle:
            for line in handle:
                if b"Submit.Success" in line:
                    continue
                found = NS.search(line)
                if found:
                    other[found.group(1).decode()] += 1
        quiet_deaths.append((name, dict(other), span))

    print()
    for name, other, span in quiet_deaths:
        print(f"`{name}` ran {span:.0f} s; non-Success events: {other}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "tmp-devnet")
