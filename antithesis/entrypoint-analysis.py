#!/usr/bin/env python3
"""
Leios Antithesis Analysis Entrypoint

Runs periodic analysis of node logs and reports assertions to Antithesis SDK.
"""

import os
import sys
import time
from datetime import datetime

# Import Antithesis SDK - handles gracefully if not available
try:
    from antithesis.lifecycle import setup_complete
    from antithesis.assertions import always, always_or_unreachable, sometimes

    ANTITHESIS_AVAILABLE = True
except ImportError:
    ANTITHESIS_AVAILABLE = False
    print("Antithesis SDK not available - running in local mode")

from analyse import compute_metrics, get_latency_stats


def log(msg: str):
    """Log with timestamp."""
    ts = datetime.now().isoformat()
    print(f"[{ts}] {msg}", flush=True)


def report_assertions(metrics, praos_threshold_ms: float, prev_max_slot: int, prev_max_slot_by_node: dict = None):
    """Report assertions to Antithesis SDK or stdout."""
    praos_stats = get_latency_stats(metrics.praos_latencies_ms)

    # --- Existing assertions ---

    # Praos block diffusion latency assertion
    if praos_stats["count"] > 0:
        praos_ok = (
            praos_stats["p95_ms"] is not None
            and praos_stats["p95_ms"] < praos_threshold_ms
        )
        message = f"Praos block diffusion p95 latency ({praos_stats['p95_ms']:.1f}ms) < {praos_threshold_ms}ms"

        if ANTITHESIS_AVAILABLE:
            always(
                praos_ok,
                message,
                {
                    "p95_latency_ms": praos_stats["p95_ms"],
                    "threshold_ms": praos_threshold_ms,
                    "sample_count": praos_stats["count"],
                },
            )
        else:
            status = "PASS" if praos_ok else "FAIL"
            log(f"[{status}] {message}")

    # Leios EBs created assertion (sometimes)
    if ANTITHESIS_AVAILABLE:
        sometimes(
            metrics.leios_ebs_created > 0,
            "Leios endorser blocks (EBs) were created",
            {
                "ebs_created": metrics.leios_ebs_created,
            },
        )
    else:
        log(f"Leios blocks created: EBs={metrics.leios_ebs_created}")

    # Praos blocks flowing assertion
    if ANTITHESIS_AVAILABLE:
        always(
            metrics.praos_blocks_received > 0 or metrics.praos_blocks_created == 0,
            "Praos blocks are being received when created",
            {
                "created": metrics.praos_blocks_created,
                "received": metrics.praos_blocks_received,
            },
        )
    else:
        if metrics.praos_blocks_created > 0 and metrics.praos_blocks_received == 0:
            log("[WARN] Praos blocks created but none received")

    # --- New assertions ---

    # Per-pool block production (sometimes) — chain quality
    for pool_name in ["pool1", "pool2", "pool3"]:
        pool_count = metrics.blocks_created_by_node.get(pool_name, 0)
        if ANTITHESIS_AVAILABLE:
            sometimes(
                pool_count > 0,
                f"{pool_name} produces blocks",
                {
                    "pool": pool_name,
                    "blocks_created": pool_count,
                },
            )
        else:
            log(f"  {pool_name} blocks created: {pool_count}")

    # Chain quality / fairness: no single pool dominates block production
    total_blocks = sum(metrics.blocks_created_by_node.values())
    if total_blocks > 10:
        max_share = max(metrics.blocks_created_by_node.values()) / total_blocks
        fair = max_share <= 0.6
        if ANTITHESIS_AVAILABLE:
            always(
                fair,
                "No pool produces more than 60% of blocks",
                {
                    "max_share": round(max_share, 3),
                    "total_blocks": total_blocks,
                    "per_pool": dict(metrics.blocks_created_by_node),
                },
            )
        else:
            status = "PASS" if fair else "FAIL"
            log(f"[{status}] Max pool share: {max_share:.1%} (threshold 60%)")

    # Chain growth (sometimes) — chain tip advances between checks
    chain_advanced = metrics.max_slot_seen > prev_max_slot
    if ANTITHESIS_AVAILABLE:
        sometimes(
            chain_advanced,
            "Chain tip advances between checks",
            {
                "prev_max_slot": prev_max_slot,
                "current_max_slot": metrics.max_slot_seen,
            },
        )
    else:
        status = "advancing" if chain_advanced else "stalled"
        log(f"  Chain: slot {prev_max_slot} -> {metrics.max_slot_seen} ({status})")

    # Per-node slot advancement (sometimes) — no stuck nodes
    if prev_max_slot_by_node is not None:
        for pool_name in ["pool1", "pool2", "pool3"]:
            cur_slot = metrics.max_slot_by_node.get(pool_name, 0)
            prev_slot = prev_max_slot_by_node.get(pool_name, 0)
            advanced = cur_slot > prev_slot
            if ANTITHESIS_AVAILABLE:
                sometimes(
                    advanced,
                    f"{pool_name} slot advances between checks",
                    {
                        "pool": pool_name,
                        "prev_slot": prev_slot,
                        "current_slot": cur_slot,
                    },
                )
            else:
                status = "advancing" if advanced else "stalled"
                log(f"  {pool_name}: slot {prev_slot} -> {cur_slot} ({status})")

    # Leios votes created (sometimes)
    if ANTITHESIS_AVAILABLE:
        sometimes(
            metrics.leios_votes_created > 0,
            "Leios votes were created",
            {
                "votes_created": metrics.leios_votes_created,
            },
        )
    else:
        log(f"  Leios votes created: {metrics.leios_votes_created}")

    # --- Safety assertions ---

    # No equivocation: no node forges two blocks in same slot
    no_equivocation = len(metrics.equivocations) == 0
    if ANTITHESIS_AVAILABLE:
        always(
            no_equivocation,
            "No node forges two blocks in the same slot",
            {
                "equivocations": [
                    {"node": n, "slot": s, "hash1": h1, "hash2": h2}
                    for n, s, h1, h2 in metrics.equivocations[:5]
                ],
            },
        )
    else:
        if not no_equivocation:
            log(f"[FAIL] Equivocations detected: {metrics.equivocations}")

    # No duplicate creators: each block hash has one creator
    no_dup_creators = len(metrics.duplicate_creators) == 0
    if ANTITHESIS_AVAILABLE:
        always(
            no_dup_creators,
            "Each block has exactly one creator",
            {
                "duplicates": [
                    {"hash": h, "node1": n1, "node2": n2}
                    for h, n1, n2 in metrics.duplicate_creators[:5]
                ],
            },
        )
    else:
        if not no_dup_creators:
            log(f"[FAIL] Duplicate block creators: {metrics.duplicate_creators}")

    # Slot monotonicity: forged slots never decrease within a node
    no_regressions = len(metrics.slot_regressions) == 0
    if ANTITHESIS_AVAILABLE:
        always(
            no_regressions,
            "Forged block slots never decrease within a node",
            {
                "regressions": [
                    {"node": n, "prev_slot": ps, "new_slot": ns}
                    for n, ps, ns in metrics.slot_regressions[:5]
                ],
            },
        )
    else:
        if not no_regressions:
            log(f"[FAIL] Slot regressions: {metrics.slot_regressions}")

    # No orphan blocks: all received blocks were created by a known node
    # Use always_or_unreachable — if no blocks are received, the assertion passes vacuously
    no_orphans = len(metrics.orphan_block_hashes) == 0
    if metrics.praos_blocks_received > 0:
        if ANTITHESIS_AVAILABLE:
            always_or_unreachable(
                no_orphans,
                "All received blocks were created by a known node",
                {
                    "orphan_count": len(metrics.orphan_block_hashes),
                    "orphan_sample": list(metrics.orphan_block_hashes)[:5],
                },
            )
        else:
            if not no_orphans:
                log(f"[FAIL] Orphan blocks: {list(metrics.orphan_block_hashes)[:5]}")


def main():
    """Main analysis loop."""
    log("=== Leios Antithesis Analysis Container ===")

    # Configuration from environment
    praos_threshold_ms = float(os.environ.get("PRAOS_LATENCY_THRESHOLD_MS", "5000"))
    check_interval = int(os.environ.get("CHECK_INTERVAL_SECONDS", "5"))
    initial_wait = int(os.environ.get("INITIAL_WAIT_SECONDS", "30"))
    log_dir = os.environ.get("LOG_DIR", "/logs")

    log("Configuration:")
    log(f"  PRAOS_LATENCY_THRESHOLD_MS: {praos_threshold_ms}")
    log(f"  CHECK_INTERVAL_SECONDS: {check_interval}")
    log(f"  INITIAL_WAIT_SECONDS: {initial_wait}")
    log(f"  LOG_DIR: {log_dir}")
    log(f"  ANTITHESIS_AVAILABLE: {ANTITHESIS_AVAILABLE}")

    # Wait for nodes to start producing logs
    log(f"Waiting {initial_wait}s for nodes to initialize...")
    time.sleep(initial_wait)

    # Signal setup complete to Antithesis
    if ANTITHESIS_AVAILABLE:
        setup_complete(
            {
                "container": "analysis",
                "version": "1.0",
            }
        )
    log("Setup complete - starting analysis loop")

    iteration = 0
    prev_max_slot = 0
    prev_max_slot_by_node = None
    while True:
        iteration += 1
        log(f"--- Analysis iteration {iteration} ---")

        try:
            # Compute metrics from logs
            metrics = compute_metrics(log_dir)

            # Log summary
            log(
                f"Praos blocks: created={metrics.praos_blocks_created}, received={metrics.praos_blocks_received}"
            )
            log(
                f"Leios: EBs={metrics.leios_ebs_created}, votes={metrics.leios_votes_created}"
            )
            log(
                f"Per-pool: {dict(metrics.blocks_created_by_node)}"
            )
            log(
                f"Safety: equivocations={len(metrics.equivocations)}, "
                f"dup_creators={len(metrics.duplicate_creators)}, "
                f"slot_regressions={len(metrics.slot_regressions)}, "
                f"orphan_blocks={len(metrics.orphan_block_hashes)}"
            )

            praos_stats = get_latency_stats(metrics.praos_latencies_ms)
            if praos_stats["count"] > 0:
                log(
                    f"Praos latency: avg={praos_stats['avg_ms']:.1f}ms, p95={praos_stats['p95_ms']:.1f}ms, max={praos_stats['max_ms']:.1f}ms"
                )

            # Report assertions
            report_assertions(metrics, praos_threshold_ms, prev_max_slot, prev_max_slot_by_node)
            prev_max_slot = metrics.max_slot_seen
            prev_max_slot_by_node = dict(metrics.max_slot_by_node)

        except Exception as e:
            log(f"Error in analysis: {e}")
            import traceback

            traceback.print_exc()

        time.sleep(check_interval)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        log("Shutting down...")
        sys.exit(0)
