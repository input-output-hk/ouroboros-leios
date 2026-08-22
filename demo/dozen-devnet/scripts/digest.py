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
STACK = re.compile(rb'\\"stack\\":\\"([^\\]+)')
DURATION = re.compile(rb'\\"duration\\":([0-9.eE+-]+)')
EB_SIZE = re.compile(rb'\\"ebSize\\":(\d+)')
EB_HASH = re.compile(rb'\\"ebHash\\":\\"([^\\]+)')
RB_HASH = re.compile(rb'\\"rbHash\\":\\"([^\\]+)')

# maxTxsPerEb = (maxMsgLeiosBlockBytesSize - 5) / minEbItemBytesSize, i.e. how
# many (hash, size) pairs fit in one 500 kB announcement. The EB body carries
# 36 B per transaction regardless of how big the transactions are, so this
# bound — and the tx/s it implies — is independent of transaction size.
MAX_TXS_PER_EB = (500_000 - 5) // 36


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
    print(
        "| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |"
    )
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

    forge_loop(run_dir)
    endorser_blocks(run_dir)


def forge_loop(run_dir):
    """Every phase of the forge loop, by call stack.

    Forge time lands on block delay and block delay on missed slots, so what
    matters is not the total but which phase owns it — and that changes as the
    loop is optimized. Reported per stack rather than per name so a child is
    never mistaken for its parent's whole cost.
    """
    print("\n## Forge loop, by call stack\n")
    print("A leader slot runs the whole tree; a non-leader slot stops after the")
    print("leadership check, so `n` differs between rows by design.\n")
    print("| stack | n | p50 | p95 | max |")
    print("| --- | --- | --- | --- | --- |")
    per_stack = collections.defaultdict(list)
    for path in sorted(glob.glob(os.path.join(run_dir, "bp*", "node.log"))):
        with open(path, "rb") as handle:
            for line in handle:
                if b"Forge.Loop.Call" not in line or b'\\"event\\":\\"End' not in line:
                    continue
                stack, duration = STACK.search(line), DURATION.search(line)
                if stack and duration:
                    per_stack[stack.group(1).decode()].append(float(duration.group(1)))
    for stack, values in sorted(
        per_stack.items(), key=lambda kv: -statistics.median(kv[1])
    ):
        values.sort()
        p50, p95, worst = (
            quantiles_at(values, 0.5),
            quantiles_at(values, 0.95),
            values[-1],
        )
        # Indent children under their parent so the tree stays readable.
        depth = stack.count(" -> ")
        label = ("&nbsp;" * 4 * depth) + stack.rsplit(" -> ", 1)[-1]
        print(
            f"| {label} | {len(values)} | {p50:.3f} s | {p95:.3f} s | {worst:.3f} s |"
        )


def quantiles_at(sorted_values, fraction):
    return sorted_values[
        min(int(len(sorted_values) * fraction), len(sorted_values) - 1)
    ]


def votes_withheld(run_dir):
    """Why nodes declined to vote — the most diagnostic number in a loaded run.

    An EB is certifiable only by the block succeeding its announcement, so a vote
    has one inter-block interval to be produced and diffused. Miss that and the EB
    is unrecoverable. Under load this is what actually caps throughput: EBs stay
    97% full and re-endorsement works as designed, but `tooLate` climbs and fewer
    certificates form. It is downstream of forge latency — a voter stalled in a
    multi-second mempool walk votes after the certifying block is already made.

    Read this alongside the forge loop table: `tooLate` rising and
    `partition-mempool` p95 rising are the same event seen from two ends.
    """
    reason = re.compile(rb'\\"reason\\":\\"([^\\]+)')
    tally = collections.Counter()
    voted = 0
    for path in glob.glob(os.path.join(run_dir, "*", "node.log")):
        with open(path, "rb") as handle:
            for line in handle:
                if b"LeiosNotVoted" in line:
                    found = reason.search(line)
                    if found:
                        tally[found.group(1).decode()] += 1
                elif b"LeiosVoted" in line:
                    voted += 1
    if not (tally or voted):
        return
    total = sum(tally.values())
    print("\n### Votes withheld\n")
    print(f"{voted} votes cast, {total} withheld", end="")
    print(
        f" — {100*total/(voted+total):.0f}% of opportunities.\n"
        if voted + total
        else ".\n"
    )
    print("| reason | n |")
    print("| --- | --- |")
    for name, count in tally.most_common():
        print(f"| `{name}` | {count} |")


def endorser_blocks(run_dir):
    """EB fill and certification rate.

    Fill is read from the forge trace's own tx count, not inferred from confirmed
    throughput — dividing chain-wide throughput by a per-node trace count once
    produced a fill figure three times too low.
    """
    print("\n## Endorser blocks\n")
    forged, announced, certified = [], set(), set()
    for path in sorted(glob.glob(os.path.join(run_dir, "*", "node.log"))):
        producer = os.path.basename(os.path.dirname(path)).startswith("bp")
        with open(path, "rb") as handle:
            for line in handle:
                if producer and b"LeiosKernel.BlockForged" in line:
                    txs, size = NUM_TXS.search(line), EB_SIZE.search(line)
                    if txs and size:
                        forged.append((int(txs.group(1)), int(size.group(1))))
                elif b"LeiosKernel.AnnouncementAccepted" in line:
                    found = EB_HASH.search(line)
                    if found:
                        announced.add(found.group(1))
                elif b"LeiosKernel.Certified" in line:
                    found = RB_HASH.search(line)
                    if found:
                        certified.add(found.group(1))

    if forged:
        counts = sorted(t for t, _ in forged)
        print(f"{len(forged)} EBs forged across the block producers.\n")
        print("| | txs | % of maxTxsPerEb | body bytes |")
        print("| --- | --- | --- | --- |")
        for label, fraction in (("p50", 0.5), ("p95", 0.95)):
            txs = quantiles_at(counts, fraction)
            print(f"| {label} | {txs} | {100*txs/MAX_TXS_PER_EB:.0f}% | {txs*36} |")
        print(
            f"| max | {counts[-1]} | {100*counts[-1]/MAX_TXS_PER_EB:.0f}% | {counts[-1]*36} |"
        )
        full = sum(1 for t in counts if t > 0.9 * MAX_TXS_PER_EB)
        print(f"\n{full}/{len(counts)} over 90% full (maxTxsPerEb = {MAX_TXS_PER_EB}).")

    votes_withheld(run_dir)

    # Distinct hashes, because every node traces every announcement it accepts and
    # a raw line count would be per-node observations rather than a chain figure.
    if announced:
        rate = 100 * len(certified) / len(announced)
        print(
            f"\n{len(announced)} distinct EBs announced, {len(certified)} certifying blocks seen — {rate:.0f}%."
        )
        print(
            "\nCertification cannot reach 100%: an EB is only certifiable by an RB at"
        )
        print("least `minCertificationGap` slots after the announcing one, so with")
        print("Poisson block arrival a share of announcements never gets a qualifying")
        print("slot. That share, not EB fill, is the gap to the full-EB ceiling.")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "tmp-devnet")
