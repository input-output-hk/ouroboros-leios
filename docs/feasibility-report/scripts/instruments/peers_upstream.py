#!/usr/bin/env python3
"""Upstream peers of the IOG and PIR hosts (report section 6.3), from the
per-peer announcement events pulled from the IOG monitoring
(Consensus.LeiosPeer.Announcement, one line per peer that announced an EB
to the node; DATA.md), under the same definition the diffusion instrument
applies to the operators' nodes: the number of distinct peers
(peer.connectionId) that delivered announcements during the period.

    peers_upstream.py PULL_DIR T0 T1 > upstream_hosts.csv

PULL_DIR  the pull folder, one <host>_peers.jsonl.zst (or .jsonl) per host
T0, T1    the period, UTC 'YYYY-MM-DDTHH:MM:SS'
Writes agent,upstream; diffusion_bins.py reads it next to diffusion.csv and
uses it for the hosts whose own records carry no peer.
"""
import csv, datetime as dt, glob, json, os, subprocess, sys


def records(path):
    if path.endswith(".zst"):
        p = subprocess.Popen(["zstd", "-dc", path], stdout=subprocess.PIPE)
        for line in p.stdout:
            yield json.loads(line)
        p.wait()
    else:
        for line in open(path):
            yield json.loads(line)


def main():
    d, t0, t1 = sys.argv[1], sys.argv[2], sys.argv[3]
    ts0 = int(dt.datetime.fromisoformat(t0).replace(tzinfo=dt.timezone.utc).timestamp() * 1e9)
    ts1 = int(dt.datetime.fromisoformat(t1).replace(tzinfo=dt.timezone.utc).timestamp() * 1e9)
    w = csv.writer(sys.stdout)
    w.writerow(["agent", "upstream"])
    for path in sorted(glob.glob(os.path.join(d, "*_peers.jsonl*"))):
        host = os.path.basename(path).split("_")[0]
        peers = set()
        for r in records(path):
            if ts0 <= r["ts"] < ts1:
                peer = (r.get("data") or {}).get("peer", {})
                cid = peer.get("connectionId") if isinstance(peer, dict) else None
                if cid:
                    peers.add(cid)
        w.writerow([host, len(peers)])


if __name__ == "__main__":
    main()
