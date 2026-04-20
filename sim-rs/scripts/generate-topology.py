#!/usr/bin/env python3
"""Generate a scaled topology by resampling from an existing one.

Preserves:
  - BP/relay ratio and degree distributions
  - Empirical latency profile (distance-conditioned)
  - Stake distribution shape
  - Bandwidth and CPU core counts

Algorithm:
  1. Bootstrap node locations from source (with small jitter)
  2. Assign BP/relay status at the same ratio
  3. For relays: K-NN + random links targeting source degree distribution
  4. For BPs: connect to 2 nearest relays (same as source structure)
  5. Latencies assigned by nearest-distance matching from source link pool
  6. Stake resampled from source distribution
"""

import argparse
import bisect
import heapq
import json
import math
import os
import random
import sys


def load_topology(path):
    with open(path) as f:
        return json.load(f)


def haversine_km(lon1, lat1, lon2, lat2):
    """Approximate great-circle distance in km."""
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    mlat = math.radians((lat1 + lat2) / 2)
    x = dlon * math.cos(mlat)
    return math.sqrt(x * x + dlat * dlat) * 6371


def analyze_source(topo):
    """Extract distributions and link pool from source topology."""
    nodes = topo["nodes"]

    locations = []
    relay_degrees = []
    stakes = []
    cpu_cores = []
    bandwidths = set()
    bp_count = 0

    # Collect all links with distances for latency sampling
    link_pool = []  # (distance_km, latency_ms)

    for nid, info in nodes.items():
        loc = info["location"]
        locations.append(loc)
        stake = info.get("stake", 0)
        stakes.append(stake)
        cpu_cores.append(info.get("cpu-core-count", 4))

        if stake > 0:
            bp_count += 1
        else:
            relay_degrees.append(len(info.get("producers", {})))

        for pid, link in info.get("producers", {}).items():
            bw = link.get("bandwidth-bytes-per-second", 1250000)
            bandwidths.add(bw)
            ploc = nodes[pid]["location"]
            dist = haversine_km(loc[0], loc[1], ploc[0], ploc[1])
            link_pool.append((dist, link["latency-ms"]))

    # Sort link pool by distance for bisect-based lookup
    link_pool.sort(key=lambda x: x[0])

    relay_degrees.sort()
    bp_stakes = sorted([s for s in stakes if s > 0], reverse=True)

    n = len(nodes)
    bp_ratio = bp_count / n
    bandwidth = max(bandwidths)  # use most common (typically uniform)
    cpu = max(set(cpu_cores), key=cpu_cores.count)  # mode

    return {
        "locations": locations,
        "relay_degrees": relay_degrees,
        "bp_ratio": bp_ratio,
        "bp_stakes": bp_stakes,
        "bandwidth": bandwidth,
        "cpu_cores": cpu,
        "link_pool": link_pool,
        "link_pool_dists": [lp[0] for lp in link_pool],
        "link_pool_lats": [lp[1] for lp in link_pool],
    }


def sample_latency(src, dist_km, rng):
    """Sample a latency from the source link pool for a given distance.

    Finds the nearest-distance window in the source and picks a random
    latency from that window.
    """
    dists = src["link_pool_dists"]
    lats = src["link_pool_lats"]
    n = len(dists)

    # Find insertion point and take a window around it
    idx = bisect.bisect_left(dists, dist_km)
    window = max(n // 40, 50)  # ~2.5% of pool, at least 50
    lo = max(0, idx - window // 2)
    hi = min(n, lo + window)
    if hi == n:
        lo = max(0, hi - window)

    return lats[rng.randint(lo, hi - 1)]


def k_nearest(target_idx, all_locs, k, exclude):
    """Find k nearest nodes by equirectangular distance. Returns list of indices."""
    lon1, lat1 = all_locs[target_idx]
    heap = []
    for i, (lon2, lat2) in enumerate(all_locs):
        if i == target_idx or i in exclude:
            continue
        dist = haversine_km(lon1, lat1, lon2, lat2)
        if len(heap) < k:
            heapq.heappush(heap, (-dist, i))
        elif dist < -heap[0][0]:
            heapq.heapreplace(heap, (-dist, i))
    return [idx for _, idx in heap]


def generate(source_path, target_n, seed):
    rng = random.Random(seed)

    topo = load_topology(source_path)
    src = analyze_source(topo)

    n_src = len(src["locations"])
    n_bp = max(1, round(target_n * src["bp_ratio"]))
    n_relay = target_n - n_bp

    # --- Step 1: Bootstrap node locations ---
    locs = []
    for _ in range(target_n):
        base = src["locations"][rng.randint(0, n_src - 1)]
        # Jitter: ~0.5 degree (~50km) to avoid exact duplicates
        lon = base[0] + rng.gauss(0, 0.5)
        lat = max(-90, min(90, base[1] + rng.gauss(0, 0.5)))
        locs.append([round(lon, 4), round(lat, 4)])

    # --- Step 2: Assign roles ---
    # First n_relay are relays, rest are BPs
    indices = list(range(target_n))
    rng.shuffle(indices)
    relay_indices = set(indices[:n_relay])
    bp_indices = set(indices[n_relay:])

    # --- Step 3: Sample target degrees for relays ---
    relay_list = sorted(relay_indices)
    relay_target_deg = {}
    src_deg = src["relay_degrees"]
    for ri in relay_list:
        relay_target_deg[ri] = src_deg[rng.randint(0, len(src_deg) - 1)]

    # --- Step 4: Build relay graph (K-NN + random) ---
    # Split: ~60% close, ~40% random (typical for this kind of topology)
    relay_locs = [(i, locs[i]) for i in relay_list]
    relay_set = set(relay_list)

    producers = {i: {} for i in range(target_n)}

    print(f"Building relay graph ({n_relay} relays)...", file=sys.stderr)
    for ri in relay_list:
        deg = relay_target_deg[ri]
        n_close = max(1, round(deg * 0.6))
        n_random = deg - n_close

        # K-NN among relays
        close = k_nearest(ri, locs, n_close, exclude=bp_indices)
        peers = set(close)

        # Random relay peers
        candidates = [r for r in relay_list if r != ri and r not in peers]
        if candidates and n_random > 0:
            rand_peers = rng.sample(candidates, min(n_random, len(candidates)))
            peers.update(rand_peers)

        for pi in peers:
            dist = haversine_km(locs[ri][0], locs[ri][1], locs[pi][0], locs[pi][1])
            lat = sample_latency(src, dist, rng)
            producers[ri][pi] = round(lat, 4)
            # Symmetrize: ensure the reverse link exists too
            if ri not in producers[pi]:
                producers[pi][ri] = round(lat, 4)

    # --- Step 5: Connect BPs to 2 nearest relays ---
    print(f"Connecting {n_bp} BPs to relays...", file=sys.stderr)
    for bi in sorted(bp_indices):
        nearest = k_nearest(bi, locs, 2, exclude=bp_indices)
        for pi in nearest:
            dist = haversine_km(locs[bi][0], locs[bi][1], locs[pi][0], locs[pi][1])
            lat = sample_latency(src, dist, rng)
            producers[bi][pi] = round(lat, 4)
            if bi not in producers[pi]:
                producers[pi][bi] = round(lat, 4)

    # --- Step 6: Assign stake ---
    bp_list = sorted(bp_indices)
    src_stakes = src["bp_stakes"]
    # Resample stakes, then normalize to original total
    raw = [src_stakes[rng.randint(0, len(src_stakes) - 1)] for _ in bp_list]
    total_src = sum(src_stakes)
    total_raw = sum(raw)
    stakes = {}
    for i, bi in enumerate(bp_list):
        stakes[bi] = max(1, round(raw[i] * total_src / total_raw))

    # --- Step 7: Emit topology ---
    print("Writing topology...", file=sys.stderr)
    bw = src["bandwidth"]
    cpu = src["cpu_cores"]

    out_nodes = {}
    for i in range(target_n):
        name = f"node-{i}"
        node = {
            "location": locs[i],
            "cpu-core-count": cpu,
            "stake": stakes.get(i, 0),
            "producers": {},
        }
        for pi, lat in sorted(producers[i].items()):
            node["producers"][f"node-{pi}"] = {
                "bandwidth-bytes-per-second": bw,
                "latency-ms": lat,
            }
        out_nodes[name] = node

    json.dump({"nodes": out_nodes}, sys.stdout, separators=(",", ":"))
    print(file=sys.stderr)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate a scaled topology by resampling from an existing one."
    )
    parser.add_argument("source", help="Path to source topology YAML/JSON file")
    parser.add_argument("target_nodes", type=int, help="Target number of nodes")
    parser.add_argument("-o", "--output", help="Output file (default: stdout)")
    parser.add_argument("-s", "--seed", type=int, default=42, help="Random seed (default: 42)")
    args = parser.parse_args()

    if args.output:
        orig_stdout = sys.stdout
        sys.stdout = open(args.output, "w")

    generate(args.source, args.target_nodes, args.seed)

    if args.output:
        sys.stdout.close()
        sys.stdout = orig_stdout
        print(f"Wrote {args.output}", file=sys.stderr)
        script_dir = os.path.dirname(os.path.abspath(__file__))
        os.system(f'{script_dir}/summarize-topology.py -1 {args.output}')
