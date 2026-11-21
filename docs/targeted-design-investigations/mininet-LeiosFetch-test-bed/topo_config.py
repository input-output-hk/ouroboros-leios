"""
Parse and provide access to a simulation configuration from input.json.

The input.json file is the single source of truth for a simulation:
network topology, injection schedule, and simulation duration.
mininet_topo.py reads it as input; plot scripts read the copy saved
in the results directory.
"""

import json


class TopoConfig:
    """Parsed simulation configuration."""

    def __init__(self, path):
        with open(path) as f:
            raw = json.load(f)

        self.nic_bw_mbit = raw["nic_bw_mbit"]
        self.default_duration = raw["default_duration"]
        self.schedule = raw["schedule"]

        self.edges = []
        for e in raw["edges"]:
            self.edges.append((
                e["a"], e["b"], e["bw_mbit"], e["delay"],
                e["jitter"], e.get("loss_gemodel"),
                e["a_pulls"], e["b_pulls"],
            ))

        self.tuned_initcwnd = set(raw.get("tuned_initcwnd", []))

        self.node_nicknames = {
            int(k): v for k, v in raw.get("node_nicknames", {}).items()
        }

        # Derive node IDs from edges.
        self.node_ids = set()
        for a, b, *_ in self.edges:
            self.node_ids.add(a)
            self.node_ids.add(b)

        # Derive OUTGOING: lower-numbered node initiates to higher.
        self._outgoing = {nid: [] for nid in self.node_ids}
        for a, b, *_ in self.edges:
            lo, hi = min(a, b), max(a, b)
            self._outgoing[lo].append(hi)
        for k in self._outgoing:
            self._outgoing[k].sort()

    def outgoing(self, node_id):
        """Peers this node initiates TCP connections to."""
        return self._outgoing.get(node_id, [])

    def peers_of(self, node_id):
        """All peers of a node (both directions)."""
        peers = set()
        for a, b, *_ in self.edges:
            if a == node_id:
                peers.add(b)
            elif b == node_id:
                peers.add(a)
        return sorted(peers)

    def link_params(self, node_id, peer_id):
        """Return (bw_mbit, delay, jitter, loss_gemodel) for an edge."""
        for a, b, bw, delay, jitter, loss, a_pulls, b_pulls in self.edges:
            if (a == node_id and b == peer_id) or (b == node_id and a == peer_id):
                return bw, delay, jitter, loss
        raise ValueError("no edge between %d and %d" % (node_id, peer_id))

    def is_downstream_only(self, node_id, peer_id):
        """True if peer_id is downstream-only from node_id's perspective.
        i.e. node_id never pulls from peer_id."""
        for a, b, _bw, _d, _j, _l, a_pulls, b_pulls in self.edges:
            if a == node_id and b == peer_id:
                return not a_pulls
            if b == node_id and a == peer_id:
                return not b_pulls
        raise ValueError("no edge between %d and %d" % (node_id, peer_id))

    def to_json(self):
        """Serialize back to the input.json dict format."""
        return {
            "nic_bw_mbit": self.nic_bw_mbit,
            "default_duration": self.default_duration,
            "edges": [
                {"a": a, "b": b, "bw_mbit": bw, "delay": d,
                 "jitter": j, "loss_gemodel": l,
                 "a_pulls": ap, "b_pulls": bp}
                for a, b, bw, d, j, l, ap, bp in self.edges
            ],
            "tuned_initcwnd": sorted(self.tuned_initcwnd),
            "node_nicknames": {str(k): v for k, v in self.node_nicknames.items()},
            "schedule": self.schedule,
        }

    def save(self, path):
        """Write input.json."""
        with open(path, "w") as f:
            json.dump(self.to_json(), f)
