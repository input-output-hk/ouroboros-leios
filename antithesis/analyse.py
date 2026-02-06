#!/usr/bin/env python3
"""
Leios Antithesis Analysis Module

Parses node logs and computes metrics for Antithesis assertions.
Adapted from demo/2025-11/analysis scripts.
"""

import json
import os
import re
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
    block_type: str  # 'praos', 'ib', 'eb', 'vote'


@dataclass
class Metrics:
    """Computed metrics from log analysis."""
    praos_blocks_created: int = 0
    praos_blocks_received: int = 0
    leios_ibs_created: int = 0
    leios_ebs_created: int = 0
    leios_votes_created: int = 0
    praos_latencies_ms: list = None
    leios_latencies_ms: list = None

    def __post_init__(self):
        if self.praos_latencies_ms is None:
            self.praos_latencies_ms = []
        if self.leios_latencies_ms is None:
            self.leios_latencies_ms = []


def parse_timestamp(ts_str: str) -> Optional[datetime]:
    """Parse various timestamp formats from logs."""
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
        ts = parse_timestamp(data.get('at', data.get('timestamp', '')))
        if not ts:
            return None

        msg = data.get('msg', data.get('message', ''))

        # Praos block events
        if 'TraceAddBlockEvent' in str(data) or 'AddedToCurrentChain' in msg:
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type='adopted',
                block_hash=data.get('block', data.get('hash', 'unknown')),
                slot=data.get('slot', 0),
                block_type='praos'
            )

        # Leios IB events
        if 'InputBlock' in msg or 'IB' in msg:
            event_type = 'created' if 'created' in msg.lower() else 'received'
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type=event_type,
                block_hash=data.get('hash', 'unknown'),
                slot=data.get('slot', 0),
                block_type='ib'
            )

        # Leios EB events
        if 'EndorserBlock' in msg or 'EB' in msg:
            event_type = 'created' if 'created' in msg.lower() else 'received'
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type=event_type,
                block_hash=data.get('hash', 'unknown'),
                slot=data.get('slot', 0),
                block_type='eb'
            )

        # Leios vote events
        if 'Vote' in msg:
            event_type = 'created' if 'created' in msg.lower() else 'received'
            return BlockEvent(
                timestamp=ts,
                node=node_name,
                event_type=event_type,
                block_hash=data.get('hash', 'unknown'),
                slot=data.get('slot', 0),
                block_type='vote'
            )

    except json.JSONDecodeError:
        # Try regex patterns for non-JSON logs
        pass

    return None


def parse_log_file(log_path: Path, node_name: str) -> list[BlockEvent]:
    """Parse all block events from a log file."""
    events = []
    try:
        with open(log_path, 'r') as f:
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

    # Parse all log files
    for log_file in log_path.glob("*.log"):
        node_name = log_file.stem
        events = parse_log_file(log_file, node_name)

        for event in events:
            # Count events
            if event.block_type == 'praos':
                if event.event_type == 'created':
                    metrics.praos_blocks_created += 1
                    block_created_times[event.block_hash] = event.timestamp
                elif event.event_type in ('received', 'adopted'):
                    metrics.praos_blocks_received += 1
                    if event.block_hash not in block_received_times:
                        block_received_times[event.block_hash] = []
                    block_received_times[event.block_hash].append(event.timestamp)

            elif event.block_type == 'ib':
                if event.event_type == 'created':
                    metrics.leios_ibs_created += 1
                    block_created_times[event.block_hash] = event.timestamp
                else:
                    if event.block_hash not in block_received_times:
                        block_received_times[event.block_hash] = []
                    block_received_times[event.block_hash].append(event.timestamp)

            elif event.block_type == 'eb':
                if event.event_type == 'created':
                    metrics.leios_ebs_created += 1

            elif event.block_type == 'vote':
                if event.event_type == 'created':
                    metrics.leios_votes_created += 1

    # Compute latencies
    for block_hash, created_time in block_created_times.items():
        if block_hash in block_received_times:
            for received_time in block_received_times[block_hash]:
                latency_ms = (received_time - created_time).total_seconds() * 1000
                if latency_ms > 0:  # Only positive latencies
                    # Determine block type from hash pattern (simplified)
                    if any(e.block_type == 'praos' for e in events if e.block_hash == block_hash):
                        metrics.praos_latencies_ms.append(latency_ms)
                    else:
                        metrics.leios_latencies_ms.append(latency_ms)

    return metrics


def get_latency_stats(latencies: list[float]) -> dict:
    """Compute statistics from latency measurements."""
    if not latencies:
        return {
            'count': 0,
            'min_ms': None,
            'max_ms': None,
            'avg_ms': None,
            'p50_ms': None,
            'p95_ms': None,
            'p99_ms': None,
        }

    sorted_latencies = sorted(latencies)
    n = len(sorted_latencies)

    return {
        'count': n,
        'min_ms': sorted_latencies[0],
        'max_ms': sorted_latencies[-1],
        'avg_ms': sum(sorted_latencies) / n,
        'p50_ms': sorted_latencies[n // 2],
        'p95_ms': sorted_latencies[int(n * 0.95)],
        'p99_ms': sorted_latencies[int(n * 0.99)],
    }


if __name__ == "__main__":
    # Simple test
    metrics = compute_metrics()
    print(f"Praos blocks created: {metrics.praos_blocks_created}")
    print(f"Praos blocks received: {metrics.praos_blocks_received}")
    print(f"Leios IBs created: {metrics.leios_ibs_created}")
    print(f"Leios EBs created: {metrics.leios_ebs_created}")
    print(f"Leios votes created: {metrics.leios_votes_created}")

    praos_stats = get_latency_stats(metrics.praos_latencies_ms)
    print(f"Praos latency stats: {praos_stats}")
