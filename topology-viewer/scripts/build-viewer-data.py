#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["pyyaml"]
# ///
"""Pre-compute viewer-ready JSON from topology-v4-{mini,mainnet}.yaml.

For each topology produces ONE JSON file in topology-viewer/public/data/ containing:
  - meta:               total nodes / edges / stake / bidir / literal share
  - nodes[]:            id, lon, lat, kind, stake, provider, tier, asn, cc,
                        region, ticker, pool_id, peer_count, spread_km
  - corridors_country:  per-country-pair {from, to, count, mean_latency}
  - corridors_provider: per-provider-pair {from, to, count, mean_latency}
  - corridors_continent: per-continent-pair {from, to, count, mean_latency}

Keeps file sizes small by:
  - quantising coordinates to 4 decimals
  - quantising latencies to 0.1 ms
  - aggregating ~210k edges down to ≤ a few hundred corridor entries
"""

import json
import math
import os
import sys
from collections import defaultdict
from pathlib import Path

import yaml


# Datacentre coordinates by region label.  Mirrors REGION_COORDS in
# sim-rs/scripts/generate-fused-topology.py.  The viewer uses these (and
# the country-capital fallback below) to OVERRIDE node coords from the
# topology YAML, because BPs in the YAML are placed at the geographic
# centroid of their relays — which lands in the ocean for multi-region
# pools (e.g. a pool with one EU and one US relay → BP centroid in the
# mid-Atlantic).  For viewer purposes we want each node on land at a
# plausible location.
REGION_COORDS = {
    "aws:us-east-1": (-77.46, 38.95), "aws:us-east-2": (-83.00, 39.96),
    "aws:us-west-1": (-121.89, 37.34), "aws:us-west-2": (-122.68, 45.52),
    "aws:ca-central-1": (-73.55, 45.50),
    "aws:eu-west-1": (-6.27, 53.35), "aws:eu-west-2": (-0.13, 51.51),
    "aws:eu-west-3": (2.35, 48.86), "aws:eu-central-1": (8.68, 50.11),
    "aws:eu-central-2": (8.55, 47.37), "aws:eu-north-1": (18.06, 59.33),
    "aws:eu-south-1": (9.19, 45.46),
    "aws:ap-northeast-1": (139.69, 35.69), "aws:ap-northeast-2": (126.98, 37.57),
    "aws:ap-northeast-3": (135.50, 34.69), "aws:ap-south-1": (72.88, 19.08),
    "aws:ap-southeast-1": (103.85, 1.29), "aws:ap-southeast-2": (151.21, -33.87),
    "aws:af-south-1": (18.42, -33.93), "aws:sa-east-1": (-46.63, -23.55),
    "aws:me-south-1": (50.59, 26.07),
    "gcp:us-east1": (-80.93, 33.21), "gcp:us-east4": (-77.46, 38.95),
    "gcp:us-central1": (-95.86, 41.26), "gcp:us-west1": (-120.74, 45.60),
    "gcp:us-west2": (-118.24, 34.05), "gcp:us-west3": (-111.89, 40.76),
    "gcp:us-west4": (-115.14, 36.17),
    "gcp:europe-west1": (3.83, 50.45), "gcp:europe-west2": (-0.13, 51.51),
    "gcp:europe-west3": (8.68, 50.11), "gcp:europe-west4": (5.79, 53.44),
    "gcp:europe-west6": (8.55, 47.37), "gcp:europe-west9": (2.35, 48.86),
    "gcp:europe-north1": (24.93, 60.17), "gcp:europe-southwest1": (-3.70, 40.42),
    "gcp:asia-east1": (120.96, 23.69), "gcp:asia-east2": (114.16, 22.31),
    "gcp:asia-northeast1": (139.69, 35.69), "gcp:asia-northeast3": (126.98, 37.57),
    "gcp:asia-southeast1": (103.85, 1.29), "gcp:asia-southeast2": (106.85, -6.21),
    "gcp:asia-south1": (72.88, 19.08),
    "gcp:australia-southeast1": (151.21, -33.87),
    "gcp:southamerica-east1": (-46.63, -23.55),
    "gcp:southamerica-west1": (-70.65, -33.46),
    "gcp:northamerica-northeast2": (-79.38, 43.65),
    "gcp:africa-south1": (28.04, -26.20),
    "azure:eastus": (-79.40, 37.20), "azure:eastus2": (-78.65, 36.85),
    "azure:westus": (-122.42, 37.78), "azure:westus2": (-119.85, 47.23),
    "azure:westus3": (-112.07, 33.45), "azure:northeurope": (-6.27, 53.35),
    "azure:westeurope": (4.89, 52.37), "azure:uksouth": (-0.13, 51.51),
    "azure:centralfrance": (2.35, 48.86), "azure:francecentral": (2.35, 48.86),
    "azure:germanywc": (8.68, 50.11), "azure:swedencentral": (17.64, 59.85),
    "azure:switzerlandn": (8.55, 47.37), "azure:koreacentral": (126.98, 37.57),
    "azure:southeastasia": (103.85, 1.29), "azure:centralindia": (73.86, 18.52),
    "azure:southafricanorth": (28.04, -26.20),
    "azure:mexicocentral": (-99.13, 19.43),
    "azure:malaysiawest": (101.69, 3.14),
    "ovh:de:frankfurt_am_main": (8.68, 50.11),
    "ovh:de:limburg_an_der_lahn": (8.06, 50.39),
    "ovh:de:saarland": (6.99, 49.40), "ovh:de:saarbrücken": (6.99, 49.24),
    "ovh:gb:london": (-0.13, 51.51), "ovh:gb:bexley": (0.15, 51.44),
    "ovh:ca:montreal": (-73.55, 45.50), "ovh:ca:beauharnois": (-73.88, 45.32),
    "ovh:ca:quebec": (-71.21, 46.81), "ovh:us:virginia": (-77.46, 38.95),
    "ovh:us:hillsboro": (-122.99, 45.52), "ovh:us:oakton": (-77.30, 38.89),
    "ovh:in:mumbai": (72.88, 19.08), "ovh:au:sydney": (151.21, -33.87),
    "ovh:sg:singapore": (103.85, 1.29), "ovh:pl:warsaw": (21.01, 52.23),
    "hetzner:falkenstein": (12.37, 50.48), "hetzner:helsinki": (24.93, 60.17),
    "hetzner:nuremberg": (11.08, 49.45), "hetzner:ashburn": (-77.46, 39.04),
    "hetzner:singapore": (103.85, 1.29),
    "contabo:lauterbourg": (8.18, 48.94), "contabo:st_louis": (-90.20, 38.63),
    "contabo:orangeburg": (-74.05, 41.01), "contabo:seattle": (-122.33, 47.61),
    "contabo:singapore": (103.85, 1.29), "contabo:tokyo": (139.69, 35.69),
    "contabo:sydney": (151.21, -33.87), "contabo:portsmouth": (-76.30, 36.84),
    "contabo:nuremberg": (11.08, 49.45), "contabo:karlsruhe": (8.40, 49.01),
    "contabo:frankfurt_am_main": (8.68, 50.11), "contabo:london": (-0.13, 51.51),
    "worldstream:naaldwijk": (4.20, 51.99), "leaseweb:haarlem": (4.65, 52.38),
}

# Country-capital / population-centroid fallback for nodes whose region is
# only labelled `cc:XX`.  Bounding-box centroids put many countries in the
# ocean (UK includes Channel Islands, France includes overseas territories,
# USA span has Alaska/Hawaii etc.), so we use proper city coords here.
COUNTRY_CAPITAL_COORDS = {
    "US": (-77.04, 38.91), "DE": (13.40, 52.52), "FR": (2.35, 48.86),
    "GB": (-0.13, 51.51), "NL": (4.89, 52.37), "CA": (-79.38, 43.65),
    "JP": (139.69, 35.69), "KR": (126.98, 37.57), "SG": (103.85, 1.29),
    "AU": (151.21, -33.87), "FI": (24.94, 60.17), "SE": (18.07, 59.33),
    "NO": (10.75, 59.91), "DK": (12.57, 55.68), "AT": (16.37, 48.21),
    "CH": (7.45, 46.95), "BE": (4.35, 50.85), "IT": (12.50, 41.90),
    "ES": (-3.70, 40.42), "PT": (-9.14, 38.72), "IE": (-6.27, 53.35),
    "PL": (21.01, 52.23), "CZ": (14.42, 50.09), "RU": (37.62, 55.75),
    "UA": (30.52, 50.45), "CN": (116.41, 39.90), "TW": (121.56, 25.04),
    "HK": (114.16, 22.31), "IN": (77.21, 28.61), "ID": (106.85, -6.21),
    "TH": (100.50, 13.76), "VN": (105.85, 21.02), "MY": (101.69, 3.14),
    "PH": (120.98, 14.60), "NZ": (174.78, -36.85), "BR": (-46.63, -23.55),
    "AR": (-58.38, -34.61), "MX": (-99.13, 19.43), "CL": (-70.65, -33.46),
    "ZA": (28.04, -26.20), "EG": (31.24, 30.04), "NG": (3.38, 6.45),
    "AE": (54.37, 24.45), "IL": (34.78, 32.08), "TR": (32.85, 39.93),
    "GR": (23.73, 37.98), "RO": (26.10, 44.43), "LT": (25.28, 54.69),
    "LV": (24.11, 56.95), "EE": (24.75, 59.44), "LU": (6.13, 49.61),
    "HU": (19.04, 47.50), "BG": (23.32, 42.70), "HR": (15.97, 45.81),
    "SI": (14.51, 46.06), "SK": (17.11, 48.15), "IS": (-21.94, 64.13),
    "MT": (14.51, 35.90), "CY": (33.36, 35.17), "LI": (9.52, 47.14),
    "BD": (90.40, 23.81), "PK": (73.04, 33.69), "LK": (79.86, 6.93),
    "VN": (105.85, 21.02), "KZ": (76.95, 43.24), "GE": (44.79, 41.72),
    "AM": (44.50, 40.18), "SA": (46.72, 24.71), "JO": (35.93, 31.95),
    "KW": (47.98, 29.38), "QA": (51.53, 25.29), "OM": (58.38, 23.61),
    "CO": (-74.07, 4.71), "PE": (-77.04, -12.05), "UY": (-56.16, -34.91),
    "VE": (-66.92, 10.49), "EC": (-78.51, -0.23),
    "NL": (4.89, 52.37), "BE": (4.35, 50.85),
    "MA": (-6.84, 33.97), "TN": (10.18, 36.81), "DZ": (3.04, 36.75),
    "KE": (36.82, -1.29), "GH": (-0.20, 5.56), "ET": (38.74, 9.03),
    "BG": (23.32, 42.70), "ME": (19.25, 42.44), "RS": (20.46, 44.79),
    "MK": (21.43, 41.99), "AL": (19.82, 41.33), "BA": (18.41, 43.86),
    "MD": (28.84, 47.02),
}


def viewer_coords(meta, fallback_lon, fallback_lat):
    """Return (lon, lat) preferring REGION_COORDS, then COUNTRY_CAPITAL_COORDS,
    then the topology YAML's stored coordinates.  Fixes ocean-placement of
    multi-region BPs (whose YAML location is the centroid of their relays)."""
    region = meta.get("region")
    if region and region in REGION_COORDS:
        return REGION_COORDS[region]
    if region and region.startswith("cc:"):
        cc = region[3:].upper()
        if cc in COUNTRY_CAPITAL_COORDS:
            return COUNTRY_CAPITAL_COORDS[cc]
    cc = meta.get("cc")
    if cc and cc in COUNTRY_CAPITAL_COORDS:
        return COUNTRY_CAPITAL_COORDS[cc]
    return (fallback_lon, fallback_lat)


# ISO2 country -> continent code (approximate, regional groupings).
ISO2_TO_CONTINENT = {
    # Europe
    "DE": "EU", "FR": "EU", "GB": "EU", "NL": "EU", "IT": "EU", "ES": "EU",
    "PL": "EU", "CH": "EU", "AT": "EU", "BE": "EU", "SE": "EU", "NO": "EU",
    "FI": "EU", "DK": "EU", "IE": "EU", "PT": "EU", "GR": "EU", "CZ": "EU",
    "HU": "EU", "RO": "EU", "BG": "EU", "SK": "EU", "SI": "EU", "HR": "EU",
    "LT": "EU", "LV": "EU", "EE": "EU", "LU": "EU", "MT": "EU", "CY": "EU",
    "RU": "EU", "UA": "EU", "BY": "EU", "MD": "EU", "RS": "EU", "MK": "EU",
    "AL": "EU", "BA": "EU", "ME": "EU", "IS": "EU", "LI": "EU", "AD": "EU",
    "MC": "EU", "SM": "EU", "VA": "EU",
    # North America
    "US": "NA", "CA": "NA", "MX": "NA", "CR": "NA", "PA": "NA", "GT": "NA",
    "HN": "NA", "SV": "NA", "NI": "NA", "BZ": "NA", "DO": "NA", "JM": "NA",
    "PR": "NA", "BS": "NA", "TT": "NA", "CU": "NA", "HT": "NA",
    # South America
    "BR": "SA", "AR": "SA", "CL": "SA", "CO": "SA", "PE": "SA", "VE": "SA",
    "EC": "SA", "BO": "SA", "PY": "SA", "UY": "SA", "GY": "SA", "SR": "SA",
    # Asia
    "JP": "AS", "KR": "AS", "CN": "AS", "TW": "AS", "HK": "AS", "SG": "AS",
    "IN": "AS", "ID": "AS", "TH": "AS", "VN": "AS", "MY": "AS", "PH": "AS",
    "BD": "AS", "PK": "AS", "LK": "AS", "MM": "AS", "KH": "AS", "LA": "AS",
    "MN": "AS", "KZ": "AS", "UZ": "AS", "KG": "AS", "TJ": "AS", "TM": "AS",
    "AF": "AS", "IR": "AS", "IQ": "AS", "SA": "AS", "AE": "AS", "QA": "AS",
    "KW": "AS", "BH": "AS", "OM": "AS", "YE": "AS", "JO": "AS", "LB": "AS",
    "SY": "AS", "IL": "AS", "PS": "AS", "TR": "AS", "AM": "AS", "AZ": "AS",
    "GE": "AS", "NP": "AS",
    # Africa
    "ZA": "AF", "EG": "AF", "NG": "AF", "KE": "AF", "MA": "AF", "DZ": "AF",
    "TN": "AF", "ET": "AF", "GH": "AF", "TZ": "AF", "UG": "AF", "SD": "AF",
    "AO": "AF", "MZ": "AF", "ZW": "AF", "ZM": "AF", "CD": "AF", "CG": "AF",
    "CM": "AF", "CI": "AF", "SN": "AF", "ML": "AF", "BF": "AF", "NE": "AF",
    "TD": "AF", "SO": "AF", "ER": "AF", "DJ": "AF", "RW": "AF", "BI": "AF",
    "MG": "AF", "BW": "AF", "NA": "AF", "LS": "AF", "SZ": "AF", "LY": "AF",
    "SC": "AF", "MU": "AF", "RE": "AF",
    # Oceania
    "AU": "OC", "NZ": "OC", "FJ": "OC", "PG": "OC", "NC": "OC", "VU": "OC",
    "SB": "OC", "WS": "OC", "TO": "OC", "PF": "OC",
}


def haversine_km(lon1, lat1, lon2, lat2):
    R = 6371.0
    rlat1 = math.radians(lat1)
    rlat2 = math.radians(lat2)
    dlat = rlat2 - rlat1
    dlon = math.radians(lon2 - lon1)
    a = math.sin(dlat / 2) ** 2 + math.cos(rlat1) * math.cos(rlat2) * math.sin(dlon / 2) ** 2
    return 2 * R * math.asin(math.sqrt(min(1, a)))


def compute_spread(node_lon, node_lat, peer_lonlats):
    """Mean great-circle distance from a node to its peers, in km."""
    if not peer_lonlats:
        return 0.0
    dists = [haversine_km(node_lon, node_lat, plon, plat) for plon, plat in peer_lonlats]
    return sum(dists) / len(dists)


def aggregate_corridors(nodes, key_fn):
    """Group edges by key_fn(src_node, tgt_node).  Returns list of
    {from, to, count, mean_latency, from_lon, from_lat, to_lon, to_lat}.
    The from/to coordinates are area centroids for the group."""
    bucket_edges = defaultdict(list)         # (from_key, to_key) -> [latency, ...]
    bucket_lonlats = defaultdict(list)        # key -> [(lon, lat), ...]

    for nid, info in nodes.items():
        src = info["_meta"]
        key_s = key_fn(src)
        if key_s is None:
            continue
        bucket_lonlats[key_s].append((info["location"][0], info["location"][1]))
        for peer_id, link in info.get("producers", {}).items():
            tgt = nodes[peer_id]["_meta"]
            key_t = key_fn(tgt)
            if key_t is None or key_t == key_s:
                # skip self-pair corridors (counted as "intra-bucket"; reported separately)
                pass
            if key_t is None:
                continue
            bucket_edges[(key_s, key_t)].append(link["latency-ms"])

    # Centroid per key
    centroids = {}
    for k, pts in bucket_lonlats.items():
        if not pts:
            continue
        centroids[k] = (
            round(sum(p[0] for p in pts) / len(pts), 4),
            round(sum(p[1] for p in pts) / len(pts), 4),
        )

    out = []
    for (a, b), lats in bucket_edges.items():
        if a not in centroids or b not in centroids:
            continue
        from_lon, from_lat = centroids[a]
        to_lon, to_lat = centroids[b]
        out.append({
            "from": a,
            "to": b,
            "count": len(lats),
            "mean_latency_ms": round(sum(lats) / len(lats), 1),
            "from_lon": from_lon, "from_lat": from_lat,
            "to_lon": to_lon, "to_lat": to_lat,
        })
    out.sort(key=lambda x: -x["count"])
    return out, centroids


def process_topology(yaml_path, meta_path):
    print(f"  loading {yaml_path.name}...", file=sys.stderr)
    with open(yaml_path) as f:
        data = yaml.safe_load(f)
    meta = {}
    if meta_path.exists():
        with open(meta_path) as f:
            meta = json.load(f)
    nodes = data["nodes"]
    # Stash meta on each node for the corridor aggregators and OVERRIDE the
    # YAML's location with a viewer-friendly coordinate (REGION_COORDS / capital).
    overridden = 0
    for nid, info in nodes.items():
        m = meta.get(nid, {})
        orig_lon, orig_lat = info["location"][0], info["location"][1]
        fixed_lon, fixed_lat = viewer_coords(m, orig_lon, orig_lat)
        if (abs(fixed_lon - orig_lon) > 0.5 or abs(fixed_lat - orig_lat) > 0.5):
            overridden += 1
        info["location"] = [fixed_lon, fixed_lat]
        info["_meta"] = {
            "id": nid,
            "kind": m.get("kind", "bp" if info.get("stake", 0) > 0 else "relay"),
            "provider": m.get("provider"),
            "tier": m.get("tier"),
            "asn": m.get("asn"),
            "cc": m.get("cc"),
            "region": m.get("region"),
            "ticker": m.get("ticker"),
            "pool_id": m.get("pool_id"),
            "stake": info.get("stake", 0),
            "lon": fixed_lon,
            "lat": fixed_lat,
        }
    if overridden:
        print(f"    overrode location for {overridden}/{len(nodes)} nodes "
              f"(BP centroid → region/capital)", file=sys.stderr)

    # --- Per-node arrays + spread ------------------------------------------
    out_nodes = []
    n_edges = 0
    total_stake = 0
    n_bps = 0
    bidir_count = 0
    edge_set = set()
    for nid, info in nodes.items():
        producers = info.get("producers", {})
        peer_lonlats = [tuple(nodes[p]["location"]) for p in producers if p in nodes]
        spread_km = compute_spread(info["location"][0], info["location"][1], peer_lonlats)
        m = info["_meta"]
        if m["kind"] == "bp":
            n_bps += 1
        total_stake += m["stake"]
        n_edges += len(producers)
        for p in producers:
            edge_set.add((nid, p))
        out_nodes.append({
            "id": nid,
            "lon": round(info["location"][0], 4),
            "lat": round(info["location"][1], 4),
            "kind": m["kind"],
            "stake": m["stake"],
            "provider": m["provider"],
            "tier": m["tier"],
            "asn": m["asn"],
            "cc": m["cc"],
            "region": m["region"],
            "ticker": m["ticker"] or "",
            "pool_id": m["pool_id"] or "",
            "peer_count": len(producers),
            "spread_km": round(spread_km, 1),
        })
    for (a, b) in edge_set:
        if (b, a) in edge_set:
            bidir_count += 1
    bidir_rate = bidir_count / len(edge_set) if edge_set else 0.0

    # --- Corridors ----------------------------------------------------------
    # Provider is keyed as "<provider>/<continent>" so that globally-distributed
    # providers (AWS, GCP, …) split into per-continent sub-buckets instead of
    # collapsing into a single arithmetic-mean centroid that lands in the ocean.
    def provider_region_key(m):
        p = m["provider"]
        if not p:
            return None
        cont = ISO2_TO_CONTINENT.get(m["cc"]) if m["cc"] else None
        return f"{p}/{cont}" if cont else p

    corridors_country, _ = aggregate_corridors(nodes, lambda m: m["cc"])
    corridors_provider, _ = aggregate_corridors(nodes, provider_region_key)
    corridors_continent, _ = aggregate_corridors(
        nodes, lambda m: ISO2_TO_CONTINENT.get(m["cc"]) if m["cc"] else None)

    # --- Provider tally for legend / sidebar -------------------------------
    prov_tally = defaultdict(lambda: {"nodes": 0, "stake": 0})
    for n in out_nodes:
        if n["provider"]:
            prov_tally[n["provider"]]["nodes"] += 1
            prov_tally[n["provider"]]["stake"] += n["stake"]
    prov_summary = sorted(
        [{"provider": k, "nodes": v["nodes"], "stake": v["stake"]}
         for k, v in prov_tally.items()],
        key=lambda x: -x["stake"],
    )

    out = {
        "meta": {
            "n_nodes": len(out_nodes),
            "n_bps": n_bps,
            "n_relays": len(out_nodes) - n_bps,
            "n_edges": n_edges,
            "total_stake_ada": total_stake,
            "bidir_rate": round(bidir_rate, 3),
        },
        "nodes": out_nodes,
        "corridors_country": corridors_country,
        "corridors_provider": corridors_provider,
        "corridors_continent": corridors_continent,
        "provider_summary": prov_summary,
    }
    return out


def main():
    here = Path(__file__).resolve().parent           # topology-viewer/scripts/
    viewer_root = here.parent                        # topology-viewer/
    repo_root = viewer_root.parent
    topo_dir = repo_root / "data" / "simulation" / "pseudo-mainnet"
    out_dir = viewer_root / "public" / "data"
    out_dir.mkdir(parents=True, exist_ok=True)

    targets = [
        "topology-v4-mini", "topology-v4-mainnet",
    ]

    index = []
    for stem in targets:
        yaml_path = topo_dir / f"{stem}.yaml"
        meta_path = topo_dir / f"{stem}.yaml.meta.json"
        if not yaml_path.exists():
            print(f"  ! skipping {stem}: {yaml_path} not found", file=sys.stderr)
            continue
        out = process_topology(yaml_path, meta_path)
        out_path = out_dir / f"{stem}.json"
        with open(out_path, "w") as f:
            json.dump(out, f, separators=(",", ":"))
        sz = out_path.stat().st_size / 1024
        print(f"  wrote {out_path.name} ({sz:.0f} KB)  "
              f"nodes={out['meta']['n_nodes']} edges={out['meta']['n_edges']} "
              f"country_corridors={len(out['corridors_country'])} "
              f"provider_corridors={len(out['corridors_provider'])}",
              file=sys.stderr)
        index.append({
            "id": stem,
            "label": stem.replace("topology-", ""),
            "file": f"data/{stem}.json",
            "n_nodes": out["meta"]["n_nodes"],
            "n_edges": out["meta"]["n_edges"],
        })

    with open(out_dir / "index.json", "w") as f:
        json.dump({"topologies": index}, f, indent=2)
    print(f"\nIndex: {len(index)} topologies", file=sys.stderr)


if __name__ == "__main__":
    main()
