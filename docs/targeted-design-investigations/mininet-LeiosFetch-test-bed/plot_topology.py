#!/usr/bin/env python3
"""
Render the network topology as a Graphviz diagram.

Reads mininet-results/input.json and produces topology.png.
"""

import json
import os
import subprocess
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
RESULTS_DIR = os.environ.get("RESULTS_DIR", os.path.join(SCRIPT_DIR, "mininet-results"))

def main():
    with open(os.path.join(RESULTS_DIR, "input.json")) as f:
        meta = json.load(f)

    tuned = set(meta.get("tuned_initcwnd", []))
    nicknames = {int(k): v for k, v in meta.get("node_nicknames", {}).items()}

    lines = [
        'digraph topology {',
        '  graph [fontname="Helvetica" rankdir=LR nodesep=0.6 ranksep=1.2]',
        '  node [fontname="Helvetica" shape=box style=filled fillcolor="#e8e8e8"]',
        '  edge [fontname="Helvetica" fontsize=9]',
        '',
    ]

    # Collect node IDs from edges.
    node_ids = set()
    for e in meta["edges"]:
        node_ids.add(e["a"])
        node_ids.add(e["b"])

    for nid in sorted(node_ids):
        nick = nicknames.get(nid, "")
        star = "*" if nid in tuned else ""
        label = "node%d%s\\n%s" % (nid, star, nick)
        lines.append('  n%d [label="%s"]' % (nid, label))

    lines.append('')

    # For each edge, render host-A → middlebox → host-B with the qdiscs that
    # apply on each hop's egress annotated on the connecting edge.
    for idx, e in enumerate(meta["edges"], start=1):
        a, b = e["a"], e["b"]
        bw = e["bw_mbit"]
        delay = e["delay"]
        jitter = e["jitter"]
        ge = e.get("loss_gemodel")
        loss_str = "loss ge(%g%%)" % ge[0] if ge else "0 loss"
        netem_label = "netem\\n%s ± %s\\n%s" % (delay, jitter, loss_str)
        aqm_label = "htb %d Mbit\\n+ fq_codel" % bw

        mb_id = 'mb%d' % idx
        lines.append('  %s [label="" shape=circle width=0.15 '
                     'fixedsize=true fillcolor="#606060" color="#606060"]'
                     % mb_id)

        a_pulls = e["a_pulls"]
        b_pulls = e["b_pulls"]
        # Direction annotation for "primary" traffic flow — the middlebox
        # is internally bidirectional but the topology-config arrow
        # still reflects who pulls from whom.
        if a_pulls and b_pulls:
            dir_attr = 'dir=both'
        elif a_pulls:
            dir_attr = 'dir=back'
        elif b_pulls:
            dir_attr = 'dir=forward'
        else:
            dir_attr = 'dir=none'

        # A — netem — middlebox — htb+fq_codel — B
        lines.append('  n%d -> %s [label="%s" %s arrowsize=0.8]'
                     % (a, mb_id, netem_label, dir_attr))
        lines.append('  %s -> n%d [label="%s" %s arrowsize=0.8]'
                     % (mb_id, b, aqm_label, dir_attr))

    lines.append('}')

    dot_src = '\n'.join(lines)
    out_path = os.path.join(RESULTS_DIR, "topology.png")

    result = subprocess.run(
        ['dot', '-Tpng', '-o', out_path],
        input=dot_src, text=True, capture_output=True,
    )
    if result.returncode != 0:
        print(result.stderr, file=sys.stderr)
        sys.exit(1)

    print("Wrote %s" % out_path, file=sys.stderr)


if __name__ == "__main__":
    main()
