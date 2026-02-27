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
    from antithesis.assertions import always, sometimes

    ANTITHESIS_AVAILABLE = True
except ImportError:
    ANTITHESIS_AVAILABLE = False
    print("Antithesis SDK not available - running in local mode")

from analyse import compute_metrics, get_latency_stats


def log(msg: str):
    """Log with timestamp."""
    ts = datetime.now().isoformat()
    print(f"[{ts}] {msg}", flush=True)


def report_assertions(metrics, praos_threshold_ms: float, prev_max_slot: int):
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

            praos_stats = get_latency_stats(metrics.praos_latencies_ms)
            if praos_stats["count"] > 0:
                log(
                    f"Praos latency: avg={praos_stats['avg_ms']:.1f}ms, p95={praos_stats['p95_ms']:.1f}ms, max={praos_stats['max_ms']:.1f}ms"
                )

            # Report assertions
            report_assertions(metrics, praos_threshold_ms, prev_max_slot)
            prev_max_slot = metrics.max_slot_seen

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
