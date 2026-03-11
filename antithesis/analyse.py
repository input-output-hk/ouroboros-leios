#!/usr/bin/env python3
"""
Leios Antithesis Analysis Module

Parses node logs and computes metrics for Antithesis assertions.
Adapted from demo/2025-11/analysis scripts.
"""

import json
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional


@dataclass
class BlockEvent:
    """Represents a block creation or reception event."""

    timestamp: datetime
    node: str
    event_type: str  # 'created', 'received', 'adopted'
    block_hash: str
    slot: int
    block_type: str  # 'praos', 'eb', 'vote'


@dataclass
class Metrics:
    """Computed metrics from log analysis."""

    praos_blocks_created: int = 0
    praos_blocks_received: int = 0
    leios_ebs_created: int = 0
    leios_votes_created: int = 0
    praos_latencies_ms: list = None
    blocks_created_by_node: dict = None
    max_slot_seen: int = 0
    # Safety violation tracking
    equivocations: list = None
    duplicate_creators: list = None
    slot_regressions: list = None
    orphan_block_hashes: set = None
    max_slot_by_node: dict = None

    def __post_init__(self):
        if self.praos_latencies_ms is None:
            self.praos_latencies_ms = []
        if self.blocks_created_by_node is None:
            self.blocks_created_by_node = {}
        if self.equivocations is None:
            self.equivocations = []
        if self.duplicate_creators is None:
            self.duplicate_creators = []
        if self.slot_regressions is None:
            self.slot_regressions = []
        if self.orphan_block_hashes is None:
            self.orphan_block_hashes = set()
        if self.max_slot_by_node is None:
            self.max_slot_by_node = {}


def parse_timestamp(ts_str: str) -> Optional[datetime]:
    """Parse various timestamp formats from logs."""
    # Handle nanosecond precision by truncating to microseconds
    # e.g., "2026-02-10T16:43:28.304578293Z" -> "2026-02-10T16:43:28.304578Z"
    if "." in ts_str and ts_str.endswith("Z"):
        parts = ts_str[:-1].split(".")
        if len(parts) == 2 and len(parts[1]) > 6:
            ts_str = parts[0] + "." + parts[1][:6] + "Z"

    formats = [
        "%Y-%m-%dT%H:%M:%S.%fZ",
        "%Y-%m-%dT%H:%M:%SZ",
        "%Y-%m-%d %H:%M:%S.%f",
        "%Y-%m-%d %H:%M:%S",
    ]
    for fmt in formats:
        try:
            return datetime.strptime(ts_str, fmt)
        except ValueError:
            continue
    return None


def parse_log_line(line: str, node_name: str) -> Optional[BlockEvent]:
    """Parse a single log line and extract block events."""
    try:
        # Try JSON format first
        data = json.loads(line)
        ts = parse_timestamp(data.get("at", data.get("timestamp", "")))
        if not ts:
            return None

        # Get namespace and nested data
        ns = data.get("ns", "")
        event_data = data.get("data", {})
        msg = data.get("msg", {})
        if not isinstance(msg, dict):
            msg = {}
        if not isinstance(event_data, dict):
            event_data = {}

        # Praos block adopted (cardano-node format)
        # ns: "ChainDB.AddBlockEvent.AddedToCurrentChain"
        # data.newtip: "hash@slot"
        if "AddedToCurrentChain" in ns:
            newtip = event_data.get("newtip", "")
            if "@" in newtip:
                block_hash, slot_str = newtip.rsplit("@", 1)
                try:
                    slot = int(slot_str)
                except ValueError:
                    slot = 0
            else:
                block_hash = newtip
                slot = 0
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type="adopted",
                block_hash=block_hash,
                slot=slot,
                block_type="praos",
            )

        # Praos block forged (cardano-node forge loop)
        # ns: "Forge.Loop.ForgedBlock"
        # data: {"forgedBlock": {"newBlockHash": "abc..."}, "kind": "TraceForgedBlock", "slot": 102}
        if "ForgedBlock" in ns:
            forged_data = event_data.get("forgedBlock", {})
            if not isinstance(forged_data, dict):
                forged_data = {}
            block_hash = forged_data.get(
                "newBlockHash",
                event_data.get("block", event_data.get("blockHash", "unknown")),
            )
            slot = event_data.get("slot", 0)
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type="created",
                block_hash=block_hash,
                slot=slot,
                block_type="praos",
            )

        # Block fetch completed (received from peer)
        # ns: "BlockFetch.Client.CompletedBlockFetch"
        # data.block: "hash"
        if "CompletedBlockFetch" in ns:
            block_hash = event_data.get("block", "unknown")
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type="received",
                block_hash=block_hash,
                slot=0,
                block_type="praos",
            )

        # Upstream MsgBlock send (immdb-server format)
        # msg.kind: "MsgBlock", msg.blockHash: "hash"
        if isinstance(msg, dict) and msg.get("kind") == "MsgBlock":
            block_hash = msg.get("blockHash", "unknown")
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type="created",  # upstream is the source
                block_hash=block_hash,
                slot=0,
                block_type="praos",
            )

        # Leios events
        # ns: "Consensus.LeiosKernel" with EB/Vote in data
        if "LeiosKernel" in ns or "LeiosPeer" in ns:
            kind = event_data.get("kind", "")
            if "EB" in kind or "EndorserBlock" in kind:
                event_type = (
                    "created"
                    if "created" in kind.lower() or "generate" in kind.lower()
                    else "received"
                )
                return BlockEvent(
                    timestamp=ts,
                    node=node_name,
                    event_type=event_type,
                    block_hash=event_data.get("hash", event_data.get("id", "unknown")),
                    slot=event_data.get("slot", 0),
                    block_type="eb",
                )
            if "Vote" in kind:
                event_type = (
                    "created"
                    if "created" in kind.lower() or "generate" in kind.lower()
                    else "received"
                )
                return BlockEvent(
                    timestamp=ts,
                    node=node_name,
                    event_type=event_type,
                    block_hash=event_data.get("hash", event_data.get("id", "unknown")),
                    slot=event_data.get("slot", 0),
                    block_type="vote",
                )

    except json.JSONDecodeError:
        # Try regex patterns for non-JSON logs
        pass

    return None


def parse_log_file(log_path: Path, node_name: str) -> list[BlockEvent]:
    """Parse all block events from a log file."""
    events = []
    try:
        with open(log_path, "r") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                event = parse_log_line(line, node_name)
                if event:
                    events.append(event)
    except FileNotFoundError:
        pass
    except Exception as e:
        print(f"Error parsing {log_path}: {e}")
    return events


def compute_metrics(log_dir: str = "/logs") -> Metrics:
    """
    Compute metrics from all log files in the directory.

    Returns:
        Metrics object with computed values.
    """
    log_path = Path(log_dir)
    metrics = Metrics()

    # Track block creation times for latency calculation
    block_created_times: dict[str, datetime] = {}
    block_received_times: dict[str, list[datetime]] = {}

    # Safety invariant tracking
    slots_forged: dict[str, dict[int, str]] = {}  # node -> {slot -> hash}
    block_creator: dict[str, str] = {}  # hash -> creator node
    last_forged_slot: dict[str, int] = {}  # node -> last slot forged
    created_hashes: set[str] = set()
    received_hashes: set[str] = set()

    # Parse all log files
    for log_file in log_path.glob("*.log"):
        node_name = log_file.stem
        events = parse_log_file(log_file, node_name)

        for event in events:
            # Count events
            if event.block_type == "praos":
                if event.event_type == "created":
                    metrics.praos_blocks_created += 1
                    block_created_times[event.block_hash] = event.timestamp
                    metrics.blocks_created_by_node[event.node] = (
                        metrics.blocks_created_by_node.get(event.node, 0) + 1
                    )
                    created_hashes.add(event.block_hash)
                    # Equivocation: same node, same slot, different hash
                    if event.node not in slots_forged:
                        slots_forged[event.node] = {}
                    prev_hash = slots_forged[event.node].get(event.slot)
                    if prev_hash is not None and prev_hash != event.block_hash:
                        metrics.equivocations.append(
                            (event.node, event.slot, prev_hash, event.block_hash)
                        )
                    slots_forged[event.node][event.slot] = event.block_hash
                    # Duplicate creators: same hash, different node
                    prev_creator = block_creator.get(event.block_hash)
                    if prev_creator is not None and prev_creator != event.node:
                        metrics.duplicate_creators.append(
                            (event.block_hash, prev_creator, event.node)
                        )
                    block_creator[event.block_hash] = event.node
                    # Slot monotonicity: forged slot should not decrease
                    prev_slot = last_forged_slot.get(event.node)
                    if prev_slot is not None and event.slot < prev_slot:
                        metrics.slot_regressions.append(
                            (event.node, prev_slot, event.slot)
                        )
                    last_forged_slot[event.node] = event.slot
                elif event.event_type in ("received", "adopted"):
                    metrics.praos_blocks_received += 1
                    if event.block_hash not in block_received_times:
                        block_received_times[event.block_hash] = []
                    block_received_times[event.block_hash].append(event.timestamp)
                    if event.slot > 0:
                        received_hashes.add(event.block_hash)
                if event.slot > metrics.max_slot_seen:
                    metrics.max_slot_seen = event.slot
                if event.slot > 0:
                    prev = metrics.max_slot_by_node.get(event.node, 0)
                    if event.slot > prev:
                        metrics.max_slot_by_node[event.node] = event.slot

            elif event.block_type == "eb":
                if event.event_type == "created":
                    metrics.leios_ebs_created += 1

            elif event.block_type == "vote":
                if event.event_type == "created":
                    metrics.leios_votes_created += 1

    # Compute Praos latencies
    for block_hash, created_time in block_created_times.items():
        if block_hash in block_received_times:
            for received_time in block_received_times[block_hash]:
                latency_ms = (received_time - created_time).total_seconds() * 1000
                if latency_ms > 0:  # Only positive latencies
                    metrics.praos_latencies_ms.append(latency_ms)

    # Orphan blocks: received but never created (excluding genesis)
    metrics.orphan_block_hashes = received_hashes - created_hashes

    return metrics


def get_latency_stats(latencies: list[float]) -> dict:
    """Compute statistics from latency measurements."""
    if not latencies:
        return {
            "count": 0,
            "min_ms": None,
            "max_ms": None,
            "avg_ms": None,
            "p50_ms": None,
            "p95_ms": None,
            "p99_ms": None,
        }

    sorted_latencies = sorted(latencies)
    n = len(sorted_latencies)

    return {
        "count": n,
        "min_ms": sorted_latencies[0],
        "max_ms": sorted_latencies[-1],
        "avg_ms": sum(sorted_latencies) / n,
        "p50_ms": sorted_latencies[n // 2],
        "p95_ms": sorted_latencies[int(n * 0.95)],
        "p99_ms": sorted_latencies[int(n * 0.99)],
    }


if __name__ == "__main__":
    # Simple test
    metrics = compute_metrics()
    print(f"Praos blocks created: {metrics.praos_blocks_created}")
    print(f"Praos blocks received: {metrics.praos_blocks_received}")
    print(f"Leios EBs created: {metrics.leios_ebs_created}")
    print(f"Leios votes created: {metrics.leios_votes_created}")

    praos_stats = get_latency_stats(metrics.praos_latencies_ms)
    print(f"Praos latency stats: {praos_stats}")
