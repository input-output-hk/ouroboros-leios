#!/usr/bin/env python3
"""
Improved DeltaQ analysis for Linear Leios EB diffusion.

This script implements a corrected and extended DeltaQ model for the
Linear Leios protocol's endorser block (EB) diffusion analysis.

Key improvements over the prior analysis (analysis/deltaq/linear-leios/):
  1. Correct RB structure: an RB contains EITHER transactions OR an EB
     certificate, never both.
  2. Proper block sizes: cert ~8kB, txRB ~90kB, EB body ~512kB,
     EB closure (S_EB_tx) up to 12MB.
  3. Explicit EB closure fetching: missing transactions fetched 1-hop
     from the forwarding peer (using a Markov TxCache miss model).
  4. Parametric sweep over S_EB_tx to find the practical maximum.

Approach: discretized CDF representation (10ms resolution, 40s range).
This mirrors the "Discretized" numerical backend described in the README
as an alternative to the piecewise-polynomial and Sampled backends.
"""

import math
import numpy as np
from scipy import stats
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import os
import json

# ---------------------------------------------------------------------------
# GLOBAL GRID PARAMETERS
# ---------------------------------------------------------------------------

T_MAX = 40.0  # seconds – covers all realistic completion times
N = 4000  # number of grid points
DT = T_MAX / N  # = 0.010 s per step  (10 ms resolution)

TIMES = np.arange(1, N + 1) * DT  # [DT, 2DT, ..., T_MAX]


# ---------------------------------------------------------------------------
# DISCRETIZED CDF PRIMITIVES
# ---------------------------------------------------------------------------


def cdf_never() -> np.ndarray:
    """Outcome that never finishes: CDF = 0 everywhere."""
    return np.zeros(N)


def cdf_wait(t: float) -> np.ndarray:
    """Deterministic wait: P(X <= t') = 1 if t' >= t, else 0."""
    return np.where(TIMES >= t, 1.0, 0.0)


def cdf_uniform(a: float, b: float) -> np.ndarray:
    """Uniform distribution on [a, b]."""
    if a >= b:
        return cdf_wait(a)
    return np.clip((TIMES - a) / (b - a), 0.0, 1.0)


def cdf_choice(p: float, cdf1: np.ndarray, cdf2: np.ndarray) -> np.ndarray:
    """Probabilistic choice: p * cdf1 + (1-p) * cdf2."""
    return p * cdf1 + (1.0 - p) * cdf2


def cdf_choices(weighted: list) -> np.ndarray:
    """choices [(w1, cdf1), (w2, cdf2), ...]  (weights unnormalised)."""
    total = sum(w for w, _ in weighted)
    result = np.zeros(N)
    for w, cdf in weighted:
        result += (w / total) * cdf
    return result


def _to_pdf(cdf: np.ndarray) -> np.ndarray:
    """CDF → PDF (first differences)."""
    pdf = np.empty(N)
    pdf[0] = cdf[0]
    pdf[1:] = np.diff(cdf)
    return pdf


def cdf_sequential(cdf1: np.ndarray, cdf2: np.ndarray) -> np.ndarray:
    """Sequential composition (convolution of PDFs) via FFT."""
    pdf1 = _to_pdf(cdf1)
    pdf2 = _to_pdf(cdf2)
    n2 = 2 * N
    conv = np.fft.irfft(np.fft.rfft(pdf1, n2) * np.fft.rfft(pdf2, n2), n2)[:N]
    conv = np.maximum(conv, 0.0)  # clamp FFT artefacts
    result = np.cumsum(conv)
    return np.minimum(result, 1.0)  # clamp to [0, 1]


def cdf_last_to_finish(cdf1: np.ndarray, cdf2: np.ndarray) -> np.ndarray:
    """Last-to-finish (max): P(max(X,Y) <= t) = F_X(t) * F_Y(t)."""
    return cdf1 * cdf2


def cdf_first_to_finish(cdf1: np.ndarray, cdf2: np.ndarray) -> np.ndarray:
    """First-to-finish (min): P(min(X,Y) <= t) = 1-(1-F_X)(1-F_Y)."""
    return cdf1 + cdf2 - cdf1 * cdf2


def success_within(cdf: np.ndarray, t: float) -> float:
    """P(X <= t)."""
    if t <= 0.0:
        return 0.0
    idx = min(int(t / DT) - 1, N - 1)
    return float(cdf[idx]) if idx >= 0 else 0.0


def quantile_of(cdf: np.ndarray, p: float) -> float:
    """Smallest t such that P(X <= t) >= p."""
    if p <= 0.0:
        return 0.0
    idx = int(np.searchsorted(cdf, p, side="left"))
    return float("inf") if idx >= N else (idx + 1) * DT


def failure_prob(cdf: np.ndarray) -> float:
    """P(X never completes within T_MAX)."""
    return 1.0 - float(cdf[-1])


# ---------------------------------------------------------------------------
# NETWORK MODEL
# ---------------------------------------------------------------------------

# One-way propagation delays (seconds) per distance category.
# Derived from Table 1 of the original Praos report (PraosModel.pdf §3):
# its "RTT" column gives round-trip times of 12 / 69 / 268 ms for
# short / medium / long distances; we halve those to get one-way delays
# below.  (Prior versions of this file used the Praos RTT values as OWDs,
# effectively doubling the RTT; Log 023 documents the convention fix.)
_OWD_SHORT_S = 0.006  #  6 ms one-way  →  12 ms RTT  – same datacenter / region
_OWD_MED_S = 0.0345  # 34.5 ms one-way →  69 ms RTT  – intracontinental
_OWD_LONG_S = 0.134  # 134 ms one-way → 268 ms RTT  – intercontinental

# TCP transfer-time model (selectable between Mathis-Reno and CUBIC)
# ---------------------------------------------------------------------------
# Common assumptions:
#   - Persistent TCP connection (no handshake overhead)
#   - Slow start from cwnd_0 = 10 MSS; cwnd doubles each RTT
#   - Throughput cap: 1 Gbit/s interface (125 MB/s)
#   - Packet loss p = 1e-4 (default; can be parameterised)
#
# Steady-state window (model-specific):
#   - mathis: W_ss = MSS / sqrt(p)                                  (Reno/AIMD)
#   - cubic:  W_ss = MSS · (C(4-β)/(4β))^(1/4) · p^(-3/4)             (RFC 8312)
#
# Steady-state throughputs at p = 1e-4 (Mathis: MSS/(RTT·√p); CUBIC formula
# below; rounded to 2 sig figs):
#   short  (RTT= 12 ms):  Mathis ~97 Mbps    CUBIC ~1.0 Gbps  (capped at 1 Gbit/s)
#   medium (RTT= 69 ms):  Mathis ~17 Mbps    CUBIC ~180 Mbps
#   long   (RTT=268 ms):  Mathis ~4.4 Mbps   CUBIC ~46 Mbps
#
# CUBIC's W_ss assumes the "CUBIC region" (low loss); in higher-loss conditions
# the real kernel reverts to a TCP-friendly Reno-like region, where Mathis is
# the more faithful model.
_TCP_MSS_BYTES = 1460
_TCP_CWND0_MSS = 10
_TCP_LOSS = 1e-4
_TCP_LINK_BPS = 1e9  # 1 Gbit/s

# CUBIC constants (Ha, Rhee, Xu 2008; RFC 8312)
_TCP_CUBIC_C = 0.4  # CUBIC scaling constant
_TCP_CUBIC_BETA = 0.3  # loss-fraction (Linux kernel β_kernel = 1 - 0.3 = 0.7)


def _steady_state_window(model: str, loss: float = None) -> float:
    """Steady-state TCP window (bytes) under the chosen congestion control."""
    if loss is None:
        loss = _TCP_LOSS
    if model == "mathis":
        return _TCP_MSS_BYTES / math.sqrt(loss)
    if model == "cubic":
        pre = (_TCP_CUBIC_C * (4 - _TCP_CUBIC_BETA) / (4 * _TCP_CUBIC_BETA)) ** 0.25
        return _TCP_MSS_BYTES * pre * loss ** (-0.75)
    raise ValueError(f"Unknown network model: {model!r}")


# Active network model.  Use set_network_model() to switch.
NETWORK_MODEL = "mathis"


def _tcp_transfer_time(
    size_kb: float, owd_s: float, model: str = None, loss: float = None
) -> float:
    """
    Time (seconds) for the last byte of a size_kb kB payload to arrive at
    the receiver, modelling TCP slow start followed by a model-specific
    steady-state window cap.

    In each round the sender transmits up to cwnd bytes; cwnd doubles each RTT
    until it reaches W_ss = _steady_state_window(model), after which throughput
    is congestion-control-limited.  Transmission time at link speed is
    included (relevant for short RTTs with large payloads).
    """
    if model is None:
        model = NETWORK_MODEL

    size_bytes = size_kb * 1024
    rtt = 2.0 * owd_s
    bps = _TCP_LINK_BPS / 8.0  # bytes/s

    w_ss = _steady_state_window(model, loss)
    w_max = min(w_ss, bps * rtt)  # also bounded by BDP

    t = 0.0
    sent = 0
    cwnd = _TCP_CWND0_MSS * _TCP_MSS_BYTES

    while True:
        this = min(cwnd, size_bytes - sent)
        tx_time = this / bps
        sent += this

        if sent >= size_bytes:
            return t + tx_time + owd_s  # last bit arrives at receiver

        t += rtt  # wait for ACK before next round
        cwnd = min(cwnd * 2, w_max)


# Pre-compute lookup table over the size range we care about (1 kB – 12 288 kB).
# All entries computed from _tcp_transfer_time; linear interpolation is used
# for intermediate sizes.  The table covers all sizes used in the analysis
# (up to 12 MB) so no extrapolation beyond the table maximum is needed.
# Tables are rebuilt by set_network_model() when switching between mathis/cubic.
_SIZES_KB = [1, 64, 256, 512, 1024, 2048, 4096, 6144, 8192, 10240, 12288]


def _build_transfer_table(model: str):
    """(re)Build (short, medium, long) transfer-time lookup arrays."""
    sh = [_tcp_transfer_time(s, _OWD_SHORT_S, model) for s in _SIZES_KB]
    md = [_tcp_transfer_time(s, _OWD_MED_S, model) for s in _SIZES_KB]
    lg = [_tcp_transfer_time(s, _OWD_LONG_S, model) for s in _SIZES_KB]
    return sh, md, lg


_SHORT_SEC, _MED_SEC, _LONG_SEC = _build_transfer_table(NETWORK_MODEL)


def set_network_model(model: str):
    """
    Switch the active steady-state throughput model and rebuild the lookup
    table.  All subsequently constructed CDFs will reflect the new model.
    Caller is responsible for re-running any pre-computed analyses.
    """
    global NETWORK_MODEL, _SHORT_SEC, _MED_SEC, _LONG_SEC
    if model not in ("mathis", "cubic"):
        raise ValueError(f"Unknown network model: {model!r}")
    NETWORK_MODEL = model
    _SHORT_SEC, _MED_SEC, _LONG_SEC = _build_transfer_table(model)


def _transfer_time(distance: str, size_kb: float) -> float:
    """
    Transfer time (seconds) for a payload of size_kb kB at the given distance.
    Linearly interpolates the pre-computed TCP table.  All sizes used by the
    analysis (≤ 12 MB) are covered; no extrapolation is performed.
    """
    match distance:
        case "short":
            table = _SHORT_SEC
        case "medium":
            table = _MED_SEC
        case "long":
            table = _LONG_SEC
        case _:
            raise ValueError(f"Unknown distance: {distance}")
    return float(np.interp(size_kb, _SIZES_KB, table))


def cdf_hop(size_kb: float) -> np.ndarray:
    """Single-hop CDF for transferring size_kb kB.
    Equally probable short / medium / long distances (equal weight 1/3 each).
    """
    return cdf_choices(
        [
            (1, cdf_wait(_transfer_time("short", size_kb))),
            (1, cdf_wait(_transfer_time("medium", size_kb))),
            (1, cdf_wait(_transfer_time("long", size_kb))),
        ]
    )


def cdf_hops(n: int, size_kb: float) -> np.ndarray:
    """n sequential hops for transferring size_kb kB."""
    result = cdf_hop(size_kb)
    for _ in range(n - 1):
        result = cdf_sequential(result, cdf_hop(size_kb))
    return result


# Path-length distribution from the Praos model (regular random graph)
_HOP_PROBS = [(1, 0.40), (2, 3.91), (3, 31.06), (4, 61.85), (5, 2.78)]


def cdf_blended_delay(size_kb: float) -> np.ndarray:
    """Multi-hop blended-path delay for transferring size_kb kB."""
    return cdf_choices([(p, cdf_hops(n, size_kb)) for n, p in _HOP_PROBS])


# ---------------------------------------------------------------------------
# EMPIRICAL DISTRIBUTIONS – from DeltaQ.Leios.EmpiricalDistributions
# ---------------------------------------------------------------------------


def _scale_mixture_cdf(n_max: int, mu_s: float, sigma_s: float) -> np.ndarray:
    """
    Scale-mixture (CLT) CDF for sum of k i.i.d. transactions, k~U(1,N):
        F(t) = (1/N) Σ_{k=1}^{N} Φ((t - k·μ) / (√k · σ))

    Use this when block size is itself a uniformly-distributed random variable,
    e.g. Praos blocks (apply path).  For EB closure processing where the
    validator must process ALL n_max transactions, use _fixed_n_cdf instead.
    """
    result = np.zeros(N)
    for k in range(1, n_max + 1):
        result += stats.norm.cdf(TIMES, k * mu_s, np.sqrt(k) * sigma_s)
    return result / n_max


def _fixed_n_cdf(n_txs: int, mu_s: float, sigma_s: float) -> np.ndarray:
    """
    CDF for processing exactly n_txs i.i.d. transactions (CLT approximation):
        F(t) = Φ((t - n·μ) / (√n · σ))

    Use this for EB closure validation where the closure contains a fixed
    (known) number of transactions that must ALL be processed.
    """
    if n_txs <= 0:
        return np.ones(N)  # zero work → instant completion
    mean = n_txs * mu_s
    std = max(np.sqrt(n_txs) * sigma_s, 1e-9)
    return stats.norm.cdf(TIMES, mean, std)


# Per-transaction timing constants derived from post-cip/empirical-distributions/block-edf.csv.
# Method: transaction-weighted mean of Apply[ms]/n and Reapply[ms]/n over all non-empty
# blocks (weight = n_txs × fraction-of-blocks), so each transaction in the dataset
# contributes equally.  This corrects the original Haskell constants, which were
# unweighted per-BLOCK means mistakenly used as per-tx costs (≈25× overestimate).
APPLY_MU_S = 0.000507  # 0.507 ms per tx  (tx-weighted mean of Apply[ms]/n)
APPLY_SIGMA_S = 0.000527  # 0.527 ms per tx  (tx-weighted stdev)
REAPPLY_MU_S = 0.000070  # 0.070 ms per tx  (tx-weighted mean of Reapply[ms]/n)
REAPPLY_SIGMA_S = 0.000265  # 0.265 ms per tx  (tx-weighted stdev)

# applyTxs: N=100 txs in a Praos block (unchanged from existing model)
_APPLY_TXS = _scale_mixture_cdf(100, APPLY_MU_S, APPLY_SIGMA_S)


def _n_txs_in_eb_closure(s_eb_tx_kb: float) -> int:
    """
    Number of transactions in an EB closure.

    Bounded by:
      (a) total closure size / average tx size    [S_EB_tx / avg_tx_size]
      (b) EB body tx-ref capacity                 [512kB / 32B = 16,000]

    With AVG_TX_SIZE_BYTES = 1000 the two limits coincide at
    S_EB_tx ≈ 16 MB.  For smaller EB closures the size limit dominates;
    for very large closures the hash limit caps at 16,000 txs.
    """
    n_from_size = int(s_eb_tx_kb * 1000 / AVG_TX_SIZE_BYTES)
    return max(1, min(n_from_size, EB_BODY_MAX_TX_REFS))


def validate_eb_closure_cdf(s_eb_tx_kb: float) -> np.ndarray:
    """
    CDF of the total CPU time for a voter to validate all transactions in the
    EB closure of size s_eb_tx_kb.

    Two categories of transactions must be processed:
      - Cache HITS  (fraction π₂ = 5/6): voter already validated these via
        tx-submission; only reapplyTx is needed (scripts skipped, cheap).
      - Cache MISSES (fraction π₁ = 1/6): voter fetches these for the first
        time; full applyTx is required (script execution, expensive).

    By the CLT, the total processing time for N independent transactions with
    per-tx (μ, σ²) drawn from the mixture is:

        Total ~ N( N·μ_eff, N·σ²_eff )

    where:
        μ_eff  = π₁·μ_apply  + π₂·μ_reapply
        σ²_eff = π₁·(σ²_apply + μ²_apply) + π₂·(σ²_reapply + μ²_reapply) − μ²_eff
               = π₁·σ²_apply + π₂·σ²_reapply + π₁·(μ_apply − μ_eff)² + π₂·(μ_reapply − μ_eff)²

    (Law of Total Variance; the second pair of terms is the between-component variance.)

    Single-core / sequential model — multi-core parallelism is out of scope.
    """
    n_txs = _n_txs_in_eb_closure(s_eb_tx_kb)

    mu_eff = TX_CACHE_MISS_RATE * APPLY_MU_S + TX_CACHE_HIT_RATE * REAPPLY_MU_S

    # Full mixture variance (Law of Total Variance)
    var_eff = TX_CACHE_MISS_RATE * (
        APPLY_SIGMA_S**2 + (APPLY_MU_S - mu_eff) ** 2
    ) + TX_CACHE_HIT_RATE * (REAPPLY_SIGMA_S**2 + (REAPPLY_MU_S - mu_eff) ** 2)
    sig_eff = var_eff**0.5
    return _fixed_n_cdf(n_txs, mu_eff, sig_eff)


# Keep the old name as an alias so callers in run_sensitivity_1hop_vs_blended
# and the reference model still compile; new code should use validate_eb_closure_cdf.
def reapply_txs_cdf(s_eb_tx_kb: float) -> np.ndarray:
    return validate_eb_closure_cdf(s_eb_tx_kb)


# ---------------------------------------------------------------------------
# BLOCK SIZE PARAMETERS
# ---------------------------------------------------------------------------

RB_HEADER_KB = 1  # ~1 kB header (constant size for all RBs)
CERT_RB_BODY_KB = 8  # ~8 kB: cert (≤8kB) + no transactions
TX_RB_BODY_KB = 88  # 90,112 bytes ≈ 88 kB (current mainnet S_RB)

EB_BODY_SIZES_KB = [1, 64, 256, 512]  # uniform choice: EB up to 512kB

# TxCache (Markov) miss / hit rates – from prior report Section 4.2
# p=0.5, q=0.9  →  π₁ = (1-q)/(p+1-q) = 0.1/0.6 = 1/6
# These are module-level globals that can be overridden via
# set_cache_miss_rate(pi1) for the π₁ sensitivity sweep (§5.8 in report).
TX_CACHE_MISS_RATE = 1.0 / 6.0  # π₁
TX_CACHE_HIT_RATE = 5.0 / 6.0  # π₂


def set_cache_miss_rate(pi1: float):
    """
    Override the TxCache miss rate π₁ (and update π₂ = 1 − π₁) for sensitivity
    analysis.  All subsequently constructed CDFs reflect the new rate.
    """
    global TX_CACHE_MISS_RATE, TX_CACHE_HIT_RATE
    if not (0.0 <= pi1 <= 1.0):
        raise ValueError(f"pi1 must be in [0, 1]; got {pi1}")
    TX_CACHE_MISS_RATE = float(pi1)
    TX_CACHE_HIT_RATE = 1.0 - float(pi1)


# EB body maximum tx-reference count (512kB / 32B per hash = 16,000)
EB_BODY_MAX_TX_REFS = 16_000

# Average transaction size (bytes).  CIP notes ~2000B when both limits hit;
# we use 1000B (1 kB) as a conservative assumption (more transactions).
AVG_TX_SIZE_BYTES = 1_000


# ---------------------------------------------------------------------------
# IMPROVED LEIOS MODEL
# ---------------------------------------------------------------------------


def cdf_fetch_rb_header() -> np.ndarray:
    """RB header (~1kB, always small)."""
    return cdf_blended_delay(RB_HEADER_KB)


def cdf_fetch_cert_rb_body() -> np.ndarray:
    """CertRB body (certificate, ~8kB, no transactions)."""
    return cdf_blended_delay(CERT_RB_BODY_KB)


def cdf_fetch_tx_rb_body() -> np.ndarray:
    """TxRB body (transactions, up to 90kB). Uniform choice over sizes."""
    sizes = [1, 22, 44, 88]  # kB: quarter steps up to max
    return cdf_choices([(1, cdf_blended_delay(s)) for s in sizes])


def cdf_fetch_eb_body() -> np.ndarray:
    """EB body (up to 512kB). Uniform choice over sizes."""
    return cdf_choices([(1, cdf_blended_delay(s)) for s in EB_BODY_SIZES_KB])


def cdf_fetch_missing_eb_closure(
    s_eb_tx_kb: float, use_1hop: bool = True
) -> np.ndarray:
    """
    Fetch missing EB-closure transactions.

    Model: with probability π₂ (TxCache hit) the node already holds all
    referenced transactions and incurs only a small lookup delay (1ms).
    With probability π₁ (TxCache miss) the node must fetch a fraction
    π₁ · S_EB_tx of the closure from its upstream peer.

    The README requests a "first-order approximation": treat the fetch as
    a single bulk transfer across *one* hop (the peer that forwarded the EB
    body is expected to hold the full closure).  We expose a flag to compare
    against the conservative multi-hop version.
    """
    missing_kb = TX_CACHE_MISS_RATE * s_eb_tx_kb
    if use_1hop:
        fetch_cdf = cdf_hop(missing_kb)
    else:
        fetch_cdf = cdf_blended_delay(missing_kb)
    return cdf_choice(TX_CACHE_HIT_RATE, cdf_wait(0.001), fetch_cdf)


def cdf_validate_eb_for_voter(s_eb_tx_kb: float) -> np.ndarray:
    """
    Time for a committee voter to validate an EB and cast a vote:
      1. Receive EB body  (multi-hop diffusion)
      2. Fetch missing closure txs  (1-hop)
      3. Reapply all EB-closure transactions
    """
    return cdf_sequential(
        cdf_sequential(
            cdf_fetch_eb_body(), cdf_fetch_missing_eb_closure(s_eb_tx_kb, use_1hop=True)
        ),
        reapply_txs_cdf(s_eb_tx_kb),
    )


def cdf_process_cert_rb(s_eb_tx_kb: float) -> np.ndarray:
    """
    Process an RB that contains an EB certificate (EB was certified),
    modelling the **eager** non-voter pipeline.

    Under the eager model, non-voters pre-fetch the EB body and closure
    during the diffusion window (in parallel with voter activity), so
    by the time the certRB arrives the only on-arrival work is the
    certRB body fetch + cert verify (negligible).  The non-voter
    completion time is therefore dominated by whichever finishes last:
    the pre-fetch pipeline (body + closure + reapply — equivalent to
    the voter pipeline) or the certRB body fetch itself.  In practice
    the pre-fetch pipeline dominates because the certRB body is ~8 kB.

      Parallel:
        A) Fetch certRB body                  (~8 kB blended)
        B) cdf_validate_eb_for_voter pipeline (EB body + missing
           closure + reapply, started at EB header diffusion)
    """
    pre_fetch = cdf_validate_eb_for_voter(s_eb_tx_kb)
    cert_arrival = cdf_fetch_cert_rb_body()
    return cdf_last_to_finish(pre_fetch, cert_arrival)


def cdf_process_tx_rb() -> np.ndarray:
    """
    Process an RB that contains transactions (EB was NOT certified):

      Fetch txRB body  →  Apply transactions
    """
    return cdf_sequential(cdf_fetch_tx_rb_body(), _APPLY_TXS)


def cdf_validate_rb(p_cert: float, s_eb_tx_kb: float) -> np.ndarray:
    """
    Combined RB processing time, accounting for the two cases:
      With prob p_cert:    certRB path  (EB was certified)
      With prob 1-p_cert:  txRB  path  (EB was not certified / no EB)

    This is the main improved outcome, fixing the "REVIEW" comment in
    DeltaQ.Leios that always modelled both RB-txs and EB simultaneously.
    """
    cert_path = cdf_process_cert_rb(s_eb_tx_kb)
    tx_path = cdf_process_tx_rb()
    return cdf_choice(p_cert, cert_path, tx_path)


# ---------------------------------------------------------------------------
# REFERENCE: Existing (broken) model  – for comparison
# ---------------------------------------------------------------------------


def cdf_validate_eb_existing() -> np.ndarray:
    """
    Replicate the existing 'validateEB' from DeltaQ.Leios.hs:
      (fetchTxRBBody >>. applyTxs)  ./\\.  (fetchEB >>. fetchingTxs)
      >>. reapplyTxs

    Bug: forces BOTH transaction apply AND EB validation on every RB,
    which is never the case in Linear Leios.
    """
    # "processRB": treat as a 64kB tx-RB (as in existing code, B64)
    process_rb = cdf_sequential(cdf_blended_delay(64), _APPLY_TXS)

    # "processEB": EB body (B1..B512) + simple TxCache lookup
    tx_cache = cdf_choice(5 / 6, cdf_wait(0.001), cdf_hop(1))  # 1kB miss
    process_eb = cdf_sequential(cdf_fetch_eb_body(), tx_cache)

    both = cdf_last_to_finish(process_rb, process_eb)
    # Existing model hardcodes N=2500 txs; replicate with ~2.5MB closure equivalent
    return cdf_sequential(both, reapply_txs_cdf(2500.0))


# ---------------------------------------------------------------------------
# CERTIFICATION PROBABILITY  – from Statistics.Leios / Analysis.Leios
# ---------------------------------------------------------------------------


def _stake_distribution(n_spos: int) -> np.ndarray:
    """Power-law stake distribution (same as Haskell Statistics.Praos)."""
    k = np.arange(0, n_spos + 1, dtype=float)
    return ((k + 1) / n_spos) ** 10 - (k / n_spos) ** 10


def _calibrate_committee(stakes: np.ndarray, target_m: float) -> float:
    """Find λ such that Σ_i (1-exp(-λ s_i)) = target_m (bisection)."""
    lo, hi = float(target_m), float(len(stakes))
    for _ in range(60):
        mid = (lo + hi) / 2.0
        val = np.sum(1.0 - np.exp(-mid * stakes)) - target_m
        if val < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def compute_p_certified(
    s_eb_tx_kb: float,
    n_spos: int = 2500,
    committee_size: int = 600,
    tau: float = 0.75,
    f_slot: float = 1.0 / 20.0,
    l_hdr: int = 1,
    l_vote: int = 4,
    l_diff: int = 7,
    voter_cdf_fn=None,
) -> dict:
    """
    Compute the certification probability and related quantities for a
    given EB closure size.

    Returns a dict with: p_validating, p_quorum, p_interrupted, p_certified.
    """
    L_total = 3 * l_hdr + l_vote + l_diff  # 14 slots
    L_vote_window = 3 * l_hdr + l_vote  # 7 slots  (voter deadline)

    # P_validating: voter validates EB before voting window ends
    _voter_fn = voter_cdf_fn if voter_cdf_fn is not None else cdf_validate_eb_for_voter
    voter_cdf = _voter_fn(s_eb_tx_kb)
    p_validating = success_within(voter_cdf, float(L_vote_window))

    # Stake distribution and committee calibration
    stakes = _stake_distribution(n_spos)
    lam = _calibrate_committee(stakes, float(committee_size))

    # Per-SPO success probability: p_i = p_validating × P(elected)
    p_elected = 1.0 - np.exp(-lam * stakes)
    p_i = p_validating * p_elected

    # Normal approximation of vote count
    mu_v = float(np.sum(p_i))
    sig_v = float(np.sqrt(np.sum(p_i * (1.0 - p_i))))
    threshold = tau * committee_size

    if sig_v < 1e-12:
        p_quorum = 1.0 if mu_v >= threshold else 0.0
    else:
        p_quorum = float(stats.norm.sf((threshold - mu_v) / sig_v))

    # P_interrupted: new RB arrives before L_total slots
    p_interrupted = 1.0 - np.exp(-f_slot * L_total)

    p_cert = (1.0 - p_interrupted) * p_quorum

    return dict(
        s_eb_tx_kb=s_eb_tx_kb,
        p_validating=p_validating,
        p_quorum=p_quorum,
        p_interrupted=p_interrupted,
        p_cert=p_cert,
    )


# ---------------------------------------------------------------------------
# ANALYSIS: Sweep over EB-closure sizes
# ---------------------------------------------------------------------------


def run_sweep():
    """
    Main analysis: compute outcomes for a range of S_EB_tx values.

    Metrics reported per S_EB_tx:
      p_validating  – P(voter validates EB within 7-slot window)
      p_quorum      – P(≥ τ·committee voters succeed → quorum met)
      p_cert        – P(EB certified and no early RB interruption) = p_quorum × (1-p_interrupted)
      sw14_cert     – P(certRB processed within 14s | cert path taken)
      sw7_voter     – P(voter validates EB within 7s) [same as p_validating]
      p_cert_and_safe – p_cert × sw14_cert  (EB certified AND all nodes process in time)
    """
    # Finer grid in the critical 1-2 MB region where the transition occurs
    sweep_kb = [
        0,
        128,
        256,
        384,
        512,
        640,
        768,  # 0 – 768 kB
        896,
        1024,
        1152,
        1280,  # 1 – 1.25 MB
        1408,
        1536,
        1664,
        1792,  # 1.375 – 1.75 MB
        2048,
        2560,
        3072,
        4096,  # 2 – 4 MB
        6144,
        8192,
        12288,  # 6 – 12 MB
    ]

    hdr = (
        f"{'S_EB_tx':>10}  {'p_valid':>7}  {'p_quorum':>8}  {'p_cert':>7}  "
        f"{'sw14|cert':>9}  {'p_cert×safe':>11}  "
        f"{'Q50':>6}  {'Q75':>6}  {'Q95':>6}  {'Q99':>6}"
    )
    print(hdr)
    print("-" * len(hdr))

    results = []
    tx_path_cdf = cdf_process_tx_rb()  # constant across S_EB_tx

    for s_kb in sweep_kb:
        cert_info = compute_p_certified(s_kb)
        p_cert = cert_info["p_cert"]

        cert_cdf = cdf_process_cert_rb(s_kb)
        comb_cdf = cdf_validate_rb(p_cert, s_kb)

        sw14_cert = success_within(cert_cdf, 14.0)

        # "liveness × safety": probability that EB is certified AND safely processed
        p_cert_and_safe = p_cert * sw14_cert

        row = dict(
            **cert_info,
            cdf_cert=cert_cdf,
            cdf_tx=tx_path_cdf,
            cdf_comb=comb_cdf,
            sw14_cert=sw14_cert,
            sw14_tx=success_within(tx_path_cdf, 14.0),
            sw14_comb=success_within(comb_cdf, 14.0),
            p_cert_and_safe=p_cert_and_safe,
            q50=quantile_of(comb_cdf, 0.50),
            q75=quantile_of(comb_cdf, 0.75),
            q95=quantile_of(comb_cdf, 0.95),
            q99=quantile_of(comb_cdf, 0.99),
        )
        results.append(row)

        label_mb = f"{s_kb/1024:.3f} MB"
        print(
            f"{label_mb:>10}  "
            f"{cert_info['p_validating']:>7.4f}  "
            f"{cert_info['p_quorum']:>8.4f}  "
            f"{p_cert:>7.4f}  "
            f"{sw14_cert:>9.4f}  "
            f"{p_cert_and_safe:>11.4f}  "
            f"{row['q50']:>6.2f}  "
            f"{row['q75']:>6.2f}  "
            f"{row['q95']:>6.2f}  "
            f"{row['q99']:>6.2f}"
        )

    return results


# ---------------------------------------------------------------------------
# REFERENCE RESULTS (existing model)
# ---------------------------------------------------------------------------


def run_reference():
    """Run the existing (pre-fix) model for comparison."""
    cdf = cdf_validate_eb_existing()
    print("\n--- EXISTING MODEL (for comparison) ---")
    print(f"  P(<=14s) = {success_within(cdf, 14.0):.4f}")
    print(f"  P(<=7s)  = {success_within(cdf, 7.0):.4f}")
    for q in [0.50, 0.75, 0.95, 0.99]:
        print(f"  Q{int(q*100):02d} = {quantile_of(cdf, q):.2f}s")
    return cdf


# ---------------------------------------------------------------------------
# PLOTTING
# ---------------------------------------------------------------------------

BASE_PLOT_DIR = os.path.join(os.path.dirname(__file__), "plots")
PLOT_DIR = BASE_PLOT_DIR  # rebound per-model in main(); see set_plot_subdir
os.makedirs(BASE_PLOT_DIR, exist_ok=True)


def set_plot_subdir(subdir: str = ""):
    """Set PLOT_DIR to <BASE_PLOT_DIR>/<subdir>, creating it if necessary."""
    global PLOT_DIR
    PLOT_DIR = os.path.join(BASE_PLOT_DIR, subdir) if subdir else BASE_PLOT_DIR
    os.makedirs(PLOT_DIR, exist_ok=True)


_N_SWEEP = 30  # upper bound on sweep points; updated in run_sweep if needed
COLORS = plt.cm.viridis(np.linspace(0.1, 0.9, _N_SWEEP))
L_DEADLINE = 14.0  # seconds (3*L_hdr + L_vote + L_diff)


def plot_cdf_comparison(ref_cdf, results, fname="compare_models.svg"):
    """Compare the existing model with the improved model (at S_EB_tx = 12MB)."""
    fig, ax = plt.subplots(figsize=(9, 5))

    ax.plot(TIMES, ref_cdf, "k--", lw=1.5, label="Existing model (broken)")

    # S_EB_tx = 0 (no closure needed)
    r0 = next(r for r in results if r["s_eb_tx_kb"] == 0)
    ax.plot(
        TIMES,
        r0["cdf_comb"],
        color="tab:blue",
        lw=1.5,
        label="Improved, $S_{EB-tx}$=0 (no closure)",
    )

    # S_EB_tx = 12 MB = 12288 kB
    r12 = next(r for r in results if r["s_eb_tx_kb"] == 12288)
    ax.plot(
        TIMES,
        r12["cdf_comb"],
        color="tab:orange",
        lw=1.5,
        label="Improved, $S_{EB-tx}$=12 MB",
    )

    # txRB-only path (EB not certified)
    ax.plot(
        TIMES,
        r0["cdf_tx"],
        color="tab:green",
        lw=1.5,
        ls=":",
        label="txRB path only (no EB cert)",
    )

    ax.axvline(
        L_DEADLINE, color="red", ls="--", lw=1, label=f"Deadline $L$={int(L_DEADLINE)}s"
    )
    ax.axhline(0.97, color="gray", ls=":", lw=0.8, label="97% target")

    ax.set_xlabel("Time (seconds)")
    ax.set_ylabel("CDF  –  P(complete within t)")
    ax.set_title(
        "DeltaQ: Existing vs Improved Leios Model\n"
        "(RB diffusion incl. EB-closure fetching)"
    )
    ax.legend(loc="lower right", fontsize=8)
    ax.set_xlim(0, 30)
    ax.set_ylim(0, 1.02)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    path = os.path.join(PLOT_DIR, fname)
    fig.savefig(path, format="svg")
    plt.close(fig)
    print(f"  Saved {path}")


def plot_eb_closure_sweep(results, fname="eb_closure_sweep.svg"):
    """CDF curves for all S_EB_tx values (cert path only)."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    ax1, ax2 = axes

    for i, r in enumerate(results):
        label = f"{r['s_eb_tx_kb']/1024:.1f} MB"
        ax1.plot(TIMES, r["cdf_cert"], color=COLORS[i], lw=1.2, label=label)
        ax2.plot(TIMES, r["cdf_comb"], color=COLORS[i], lw=1.2, label=label)

    for ax, title in [(ax1, "certRB path only"), (ax2, "Combined (p_cert weighted)")]:
        ax.axvline(L_DEADLINE, color="red", ls="--", lw=1)
        ax.axhline(0.97, color="gray", ls=":", lw=0.8)
        ax.set_xlabel("Time (seconds)")
        ax.set_ylabel("CDF")
        ax.set_title(f"DeltaQ sweep over $S_{{EB-tx}}$ — {title}")
        ax.set_xlim(0, 35)
        ax.set_ylim(0, 1.02)
        ax.grid(True, alpha=0.3)
        ax.legend(loc="lower right", fontsize=7, title="$S_{EB-tx}$", ncol=2)

    fig.tight_layout()
    path = os.path.join(PLOT_DIR, fname)
    fig.savefig(path, format="svg")
    plt.close(fig)
    print(f"  Saved {path}")


def plot_feasibility(results, fname="feasibility.svg"):
    """Feasibility metrics vs S_EB_tx (two subplots)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    mbs = [r["s_eb_tx_kb"] / 1024 for r in results]
    sw_cert = [r["sw14_cert"] for r in results]
    p_c = [r["p_cert"] for r in results]
    cas = [r["p_cert_and_safe"] for r in results]

    # Left: certification probability (liveness)
    ax1.plot(mbs, p_c, "o-", color="tab:blue", lw=2, label="$P_{certified}$")
    ax1.plot(
        mbs,
        sw_cert,
        "s-",
        color="tab:orange",
        lw=2,
        label="$P$(certRB validated $\\leq 14s$)",
    )
    ax1.plot(
        mbs,
        cas,
        "^-",
        color="tab:red",
        lw=2,
        label="$P_{cert} \\times P(\\leq 14s)$  (combined)",
    )
    ax1.axhline(0.20, color="gray", ls="--", lw=1, label="20% viability floor")
    ax1.set_xlabel("$S_{EB-tx}$ (MB)")
    ax1.set_ylabel("Probability")
    ax1.set_title(
        "Liveness × Safety vs $S_{EB-tx}$\n"
        "(cert path; cert-and-safe = EB certified AND processed in time)"
    )
    ax1.legend(fontsize=8)
    ax1.set_ylim(0, 0.60)
    ax1.grid(True, alpha=0.3)

    # Right: safety of the cert path only
    ax2.plot(
        mbs,
        sw_cert,
        "o-",
        color="tab:orange",
        lw=2,
        label="P(certRB validated $\\leq 14s$ | cert)",
    )
    ax2.axhline(0.97, color="red", ls="--", lw=1, label="97% target")
    ax2.axhline(0.95, color="gray", ls=":", lw=1, label="95% target")
    ax2.set_xlabel("$S_{EB-tx}$ (MB)")
    ax2.set_ylabel("P(certRB validated within 14s | cert path)")
    ax2.set_title(
        "Safety of certRB Processing\n"
        "(fraction of certRBs processed before deadline)"
    )
    ax2.legend(fontsize=9)
    ax2.set_ylim(0, 1.02)
    ax2.grid(True, alpha=0.3)

    fig.tight_layout()
    path = os.path.join(PLOT_DIR, fname)
    fig.savefig(path, format="svg")
    plt.close(fig)
    print(f"  Saved {path}")


def plot_certification(results, fname="certification.svg"):
    """p_cert and p_validating vs S_EB_tx."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4))

    mbs = [r["s_eb_tx_kb"] / 1024 for r in results]
    p_v = [r["p_validating"] for r in results]
    p_q = [r["p_quorum"] for r in results]
    p_c = [r["p_cert"] for r in results]

    ax1.plot(mbs, p_v, "o-", color="tab:blue", lw=2, label="$P_{validating}$")
    ax1.plot(mbs, p_q, "s-", color="tab:green", lw=2, label="$P_{quorum}$")
    ax1.plot(mbs, p_c, "^-", color="tab:orange", lw=2, label="$P_{certified}$")
    ax1.set_xlabel("$S_{EB-tx}$ (MB)")
    ax1.set_ylabel("Probability")
    ax1.set_title("Certification Probability vs $S_{EB-tx}$")
    ax1.legend(fontsize=9)
    ax1.set_ylim(0, 1.0)
    ax1.grid(True, alpha=0.3)

    # Quantiles
    q50 = [r["q50"] for r in results]
    q75 = [r["q75"] for r in results]
    q95 = [r["q95"] for r in results]
    q99 = [r["q99"] for r in results]
    ax2.fill_between(mbs, q50, q99, alpha=0.2, color="tab:blue", label="50th–99th pct")
    ax2.fill_between(mbs, q50, q95, alpha=0.3, color="tab:blue")
    ax2.fill_between(mbs, q50, q75, alpha=0.4, color="tab:blue")
    ax2.plot(mbs, q50, "o-", color="tab:blue", lw=2, label="Median")
    ax2.plot(mbs, q75, "s-", color="tab:orange", lw=1.5, label="75th pct")
    ax2.plot(mbs, q95, "^-", color="tab:red", lw=1.5, label="95th pct")
    ax2.plot(mbs, q99, "v-", color="purple", lw=1.5, label="99th pct")
    ax2.axhline(
        L_DEADLINE, color="red", ls="--", lw=1, label=f"Deadline {int(L_DEADLINE)}s"
    )
    ax2.set_xlabel("$S_{EB-tx}$ (MB)")
    ax2.set_ylabel("Completion time (seconds)")
    ax2.set_title("Quantiles of Combined RB Validation Time")
    ax2.legend(fontsize=8)
    ax2.grid(True, alpha=0.3)

    fig.tight_layout()
    path = os.path.join(PLOT_DIR, fname)
    fig.savefig(path, format="svg")
    plt.close(fig)
    print(f"  Saved {path}")


def plot_outcome_diagram(fname="outcome_diagram.svg"):
    """
    Schematic outcome diagram for the improved Linear Leios model.
    Two paths depending on whether the EB was certified.
    """
    fig, ax = plt.subplots(figsize=(12, 6))
    ax.set_xlim(0, 12)
    ax.set_ylim(-0.5, 6.5)
    ax.axis("off")
    ax.set_title(
        "Improved Linear Leios – RB Validation Outcome Diagram\n"
        "(fixing the 'cert XOR txs' RB structure)",
        fontsize=12,
        pad=10,
    )

    props_box = dict(boxstyle="round,pad=0.4", facecolor="#e8f4fd", edgecolor="#2980b9")
    props_op = dict(boxstyle="circle,pad=0.3", facecolor="#fdebd0", edgecolor="#e67e22")
    props_start = dict(
        boxstyle="round,pad=0.4", facecolor="#d5f5e3", edgecolor="#27ae60"
    )
    props_end = dict(boxstyle="round,pad=0.4", facecolor="#fdedec", edgecolor="#e74c3c")
    props_choice = dict(
        boxstyle="round,pad=0.3", facecolor="#f9ebea", edgecolor="#c0392b"
    )

    def box(ax, x, y, txt, props, fontsize=8, width=1.8, ha="center"):
        ax.text(x, y, txt, ha=ha, va="center", fontsize=fontsize, bbox=props, wrap=True)

    # Start
    box(ax, 1.0, 3.0, "RB header\nreceived", props_start, fontsize=8)
    ax.annotate(
        "",
        xy=(2.2, 3.0),
        xytext=(1.9, 3.0),
        arrowprops=dict(arrowstyle="->", color="black"),
    )

    # Choice diamond
    box(ax, 2.8, 3.0, "cert?\np_cert", props_choice, fontsize=7)

    # Upper branch: CERT path
    ax.annotate(
        "",
        xy=(4.0, 5.0),
        xytext=(2.8, 3.5),
        arrowprops=dict(arrowstyle="->", color="#27ae60"),
    )
    ax.text(3.1, 4.5, "yes", fontsize=7, color="#27ae60")

    box(ax, 5.0, 5.5, "Fetch\ncertRB body\n(~8 kB, blended)", props_box, fontsize=7)
    box(ax, 5.0, 4.5, "Fetch EB body\n(≤512kB, blended)", props_box, fontsize=7)
    box(
        ax,
        7.0,
        4.5,
        "Fetch missing\nEB-closure txs\n(π₁·S_EB-tx, 1-hop)",
        props_box,
        fontsize=7,
    )

    ax.annotate(
        "",
        xy=(6.1, 4.5),
        xytext=(5.9, 4.5),
        arrowprops=dict(arrowstyle="->", color="black"),
    )
    # last-to-finish of cert_rb and eb_closure
    box(ax, 8.3, 5.0, "last\nto\nfinish", props_op, fontsize=7)
    ax.annotate(
        "",
        xy=(8.0, 5.3),
        xytext=(6.0, 5.5),
        arrowprops=dict(arrowstyle="->", color="black"),
    )
    ax.annotate(
        "",
        xy=(8.0, 4.8),
        xytext=(7.9, 4.5),
        arrowprops=dict(arrowstyle="->", color="black"),
    )
    # then reapply
    box(ax, 9.5, 5.0, "Reapply EB\ntxs (≤16k tx)", props_box, fontsize=7)
    ax.annotate(
        "",
        xy=(9.0, 5.0),
        xytext=(8.6, 5.0),
        arrowprops=dict(arrowstyle="->", color="black"),
    )

    # Lower branch: TX path
    ax.annotate(
        "",
        xy=(4.0, 1.0),
        xytext=(2.8, 2.5),
        arrowprops=dict(arrowstyle="->", color="#c0392b"),
    )
    ax.text(3.1, 1.5, "no", fontsize=7, color="#c0392b")

    box(ax, 5.0, 1.0, "Fetch txRB body\n(≤90kB, blended)", props_box, fontsize=7)
    box(ax, 7.5, 1.0, "Apply txs\n(≤100 tx)", props_box, fontsize=7)
    ax.annotate(
        "",
        xy=(6.5, 1.0),
        xytext=(6.0, 1.0),
        arrowprops=dict(arrowstyle="->", color="black"),
    )

    # End
    box(ax, 10.8, 3.0, "RB\nvalidated", props_end, fontsize=8)
    ax.annotate(
        "",
        xy=(10.3, 3.0),
        xytext=(9.5, 3.5),
        arrowprops=dict(arrowstyle="->", color="black"),
    )
    ax.annotate(
        "",
        xy=(10.3, 3.0),
        xytext=(8.5, 1.2),
        arrowprops=dict(arrowstyle="->", color="black"),
    )

    # Annotations
    ax.text(
        0.1,
        6.2,
        "Key: cert path = RB holds EB certificate.  "
        "tx path = RB holds transactions.",
        fontsize=7,
        style="italic",
    )
    ax.text(
        0.1,
        5.9,
        "In the existing model these paths were incorrectly forced in parallel.",
        fontsize=7,
        color="red",
    )

    fig.tight_layout()
    path = os.path.join(PLOT_DIR, fname)
    fig.savefig(path, format="svg")
    plt.close(fig)
    print(f"  Saved {path}")


# ---------------------------------------------------------------------------
# SENSITIVITY ANALYSIS  – hop model comparison
# ---------------------------------------------------------------------------


def run_sensitivity_1hop_vs_blended():
    """Compare 1-hop vs blended-delay for missing EB closure fetching,
    under the eager non-voter model."""
    s_kb = 12288  # 12 MB

    # 1-hop (default) — non-voter pre-fetch pipeline in parallel with
    # certRB body fetch, then verify cert.
    cert_1hop = cdf_process_cert_rb(s_kb)

    # Blended-missing variant: missing-closure fetch uses blended
    # multi-hop instead of 1-hop.  Rebuild the pre-fetch pipeline with
    # the blended fetch step in place of the 1-hop step.
    eb_body = cdf_fetch_eb_body()
    missing_kb = TX_CACHE_MISS_RATE * s_kb
    blended_miss_fetch = cdf_choice(
        TX_CACHE_HIT_RATE, cdf_wait(0.001), cdf_blended_delay(missing_kb)
    )
    pre_fetch_blended = cdf_sequential(
        cdf_sequential(eb_body, blended_miss_fetch), reapply_txs_cdf(s_kb)
    )
    cert_rb = cdf_fetch_cert_rb_body()
    cert_blended = cdf_last_to_finish(pre_fetch_blended, cert_rb)

    fig, ax = plt.subplots(figsize=(8, 5))
    ax.plot(TIMES, cert_1hop, lw=2, label="1-hop fetch (recommended)")
    ax.plot(
        TIMES, cert_blended, lw=2, ls="--", label="Blended multi-hop (conservative)"
    )
    ax.axvline(
        L_DEADLINE, color="red", ls="--", lw=1, label=f"Deadline {int(L_DEADLINE)}s"
    )
    ax.set_xlabel("Time (seconds)")
    ax.set_ylabel("CDF")
    ax.set_title(
        "Sensitivity: 1-hop vs multi-hop EB-closure fetch\n($S_{EB-tx}$=12 MB)"
    )
    ax.legend(fontsize=9)
    ax.set_xlim(0, 35)
    ax.grid(True, alpha=0.3)
    ax.text(
        0.5,
        0.02,
        f"P(≤14s | 1-hop)   = {success_within(cert_1hop,14):.4f}\n"
        f"P(≤14s | blended) = {success_within(cert_blended,14):.4f}",
        transform=ax.transAxes,
        fontsize=8,
        bbox=dict(boxstyle="round", facecolor="white", alpha=0.8),
    )

    fig.tight_layout()
    path = os.path.join(PLOT_DIR, "sensitivity_1hop_vs_blended.svg")
    fig.savefig(path, format="svg")
    plt.close(fig)
    print(f"  Saved {path}")

    return {
        "1hop_sw14": success_within(cert_1hop, 14.0),
        "blended_sw14": success_within(cert_blended, 14.0),
    }


# ---------------------------------------------------------------------------
# NETWORK DIFFUSION ANALYSIS (independent of CPU)
# ---------------------------------------------------------------------------


def run_network_diffusion():
    """
    Compute network-only diffusion time for the EB closure under two models:
      (a) 1-hop approximation: node fetches only the missing fraction (π₁·S_EB_tx)
          from its upstream peer (one hop).  Justified if the raw transactions
          referenced by the EB have already diffused via tx-submission before
          the EB is produced.  (Linear Leios has no Input Blocks; transactions
          diffuse solely via tx-submission.)
      (b) Full blended diffusion: the entire S_EB_tx must traverse the blended
          multi-hop network (worst case: transactions not pre-diffused).

    CPU reapplication is NOT included – this isolates the network constraint.
    """
    sweep_kb = [512, 1024, 1536, 2048, 4096, 8192, 12288]

    rows = []
    for s_kb in sweep_kb:
        miss_kb = TX_CACHE_MISS_RATE * s_kb  # π₁ · S_EB_tx

        # (a) 1-hop for missing fraction
        net_1hop = cdf_sequential(cdf_fetch_eb_body(), cdf_hop(miss_kb))
        # (b) blended multi-hop for missing fraction
        net_miss_blended = cdf_sequential(
            cdf_fetch_eb_body(), cdf_blended_delay(miss_kb)
        )
        # (c) full closure blended (no 1-hop shortcut)
        net_full_blended = cdf_blended_delay(s_kb)

        rows.append(
            dict(
                s_kb=s_kb,
                net_1hop=net_1hop,
                net_miss_blend=net_miss_blended,
                net_full_blend=net_full_blended,
                sw7_1hop=success_within(net_1hop, 7.0),
                sw7_miss_blend=success_within(net_miss_blended, 7.0),
                sw14_full=success_within(net_full_blended, 14.0),
                sw7_full=success_within(net_full_blended, 7.0),
            )
        )
    return rows


def plot_network_diffusion(rows, fname="network_diffusion.svg"):
    """
    Three-panel plot showing network-only diffusion constraints.
    Left:  CDF for 1-hop vs full-blended model at selected sizes.
    Right: P(≤deadline) vs S_EB_tx for the three network models.
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    highlight = [512, 2048, 4096, 8192, 12288]
    colors_h = ["tab:blue", "tab:orange", "tab:green", "tab:red", "purple"]

    for row, col in zip([r for r in rows if r["s_kb"] in highlight], colors_h):
        lbl = f"{row['s_kb']/1024:.1f} MB"
        ax1.plot(
            TIMES,
            row["net_1hop"],
            color=col,
            lw=1.5,
            ls="-",
            label=f"{lbl} (1-hop miss)",
        )
        ax1.plot(TIMES, row["net_full_blend"], color=col, lw=1.5, ls="--")

    ax1.axvline(7.0, color="red", ls="--", lw=1, label="7s voter deadline")
    ax1.axvline(14.0, color="gray", ls=":", lw=1, label="14s total deadline")
    ax1.set_xlabel("Time (seconds)")
    ax1.set_ylabel("CDF")
    ax1.set_title(
        "Network-only EB-closure diffusion\n"
        "(solid=1-hop miss, dashed=full blended; no reapply)"
    )
    ax1.legend(fontsize=7, loc="lower right")
    ax1.set_xlim(0, 30)
    ax1.set_ylim(0, 1.02)
    ax1.grid(True, alpha=0.3)

    mbs = [r["s_kb"] / 1024 for r in rows]
    sw7_1hop = [r["sw7_1hop"] for r in rows]
    sw7_miss_bl = [r["sw7_miss_blend"] for r in rows]
    sw14_full = [r["sw14_full"] for r in rows]
    sw7_full = [r["sw7_full"] for r in rows]

    ax2.plot(
        mbs,
        sw7_1hop,
        "o-",
        color="tab:blue",
        lw=2,
        label="P(≤7s)  – 1-hop missing fraction",
    )
    ax2.plot(
        mbs,
        sw7_miss_bl,
        "s-",
        color="tab:orange",
        lw=2,
        label="P(≤7s)  – blended missing fraction",
    )
    ax2.plot(
        mbs,
        sw14_full,
        "^-",
        color="tab:red",
        lw=2,
        label="P(≤14s) – full closure blended (worst case)",
    )
    ax2.plot(
        mbs,
        sw7_full,
        "v-",
        color="purple",
        lw=1.5,
        ls="--",
        label="P(≤7s)  – full closure blended (worst case)",
    )

    ax2.axhline(0.97, color="red", ls="--", lw=1, label="97% target")
    ax2.set_xlabel("$S_{EB-tx}$ (MB)")
    ax2.set_ylabel("P(network fetch complete within deadline)")
    ax2.set_title(
        "Network feasibility vs $S_{EB-tx}$\n"
        "(network only; 1-hop valid only if txs pre-diffused via tx-submission)"
    )
    ax2.legend(fontsize=8, loc="lower left")
    ax2.set_ylim(0, 1.02)
    ax2.grid(True, alpha=0.3)

    fig.tight_layout()
    path = os.path.join(PLOT_DIR, fname)
    fig.savefig(path, format="svg")
    plt.close(fig)
    print(f"  Saved {path}")


# ---------------------------------------------------------------------------
# NETWORK MODEL COMPARISON PLOT
# ---------------------------------------------------------------------------


def plot_network_model_comparison(fname: str = "network_model_comparison.svg"):
    """
    Two-panel comparison of the Mathis (Reno/AIMD) and CUBIC throughput models.

    Left:  Steady-state throughput vs packet loss probability p, plotted at the
           three distance categories (short/medium/long).  Log–log scale.
    Right: Transfer time for 2 MB (S_EB_tx = 12 MB missing-closure fetch) over
           long-haul (OWD = 268 ms) vs p, with the 7 s voter deadline marked.
    """
    p_grid = np.logspace(-5, -2, 60)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    distances = [
        ("Short  (RTT=24 ms)", _OWD_SHORT_S, "tab:blue"),
        ("Medium (RTT=138 ms)", _OWD_MED_S, "tab:orange"),
        ("Long   (RTT=536 ms)", _OWD_LONG_S, "tab:red"),
    ]
    for label, owd, color in distances:
        rtt = 2.0 * owd
        # Throughput in Mbps = W_ss / RTT * 8 / 1e6
        T_m = np.array(
            [_steady_state_window("mathis", p) / rtt * 8 / 1e6 for p in p_grid]
        )
        T_c = np.array(
            [_steady_state_window("cubic", p) / rtt * 8 / 1e6 for p in p_grid]
        )
        ax1.loglog(p_grid, T_m, "-", color=color, lw=1.5, label=f"{label}, Mathis")
        ax1.loglog(p_grid, T_c, "--", color=color, lw=1.5, label=f"{label}, CUBIC")

    ax1.axvline(
        _TCP_LOSS,
        color="gray",
        ls=":",
        lw=1,
        label=f"p = {_TCP_LOSS:g} (analysis default)",
    )
    ax1.axhline(
        1e3, color="black", ls="-", lw=0.5, alpha=0.3, label="1 Gbit/s interface cap"
    )
    ax1.set_xlabel("Packet loss probability  p")
    ax1.set_ylabel("Steady-state throughput  (Mbps)")
    ax1.set_title(
        "TCP throughput response:\nMathis (T∝p$^{-1/2}$) vs CUBIC (T∝p$^{-3/4}$)"
    )
    ax1.grid(alpha=0.3, which="both")
    ax1.legend(fontsize=7, loc="lower left", ncol=2)

    # 2 MB long-haul transfer time vs p, with the 7s deadline annotated.
    # 2 MB is the S_EB_tx=12 MB missing-closure fetch (π₁·12MB = 2MB).
    t_m = np.array([_tcp_transfer_time(2048, _OWD_LONG_S, "mathis", p) for p in p_grid])
    t_c = np.array([_tcp_transfer_time(2048, _OWD_LONG_S, "cubic", p) for p in p_grid])

    ax2.semilogx(p_grid, t_m, "-", color="tab:red", lw=2, label="Mathis")
    ax2.semilogx(p_grid, t_c, "--", color="tab:red", lw=2, label="CUBIC")

    ax2.axhline(7.0, color="red", ls=":", lw=1.2, label="7 s voter deadline")
    ax2.axvline(
        _TCP_LOSS,
        color="gray",
        ls=":",
        lw=1,
        label=f"p = {_TCP_LOSS:g} (analysis default)",
    )
    # Highlight where each model crosses the 7s deadline.  Compute the
    # crossing on a separate fine grid (so it matches §5.4's table to
    # displayed precision and isn't biased by the visible curve's
    # coarser sampling, which is intentionally undersampled to look
    # smooth despite the step structure of _tcp_transfer_time).
    p_fine = np.logspace(-5, -2, 6000)
    for fn_name, name in [("mathis", "Mathis"), ("cubic", "CUBIC")]:
        t_fine = np.array(
            [_tcp_transfer_time(2048, _OWD_LONG_S, fn_name, p) for p in p_fine]
        )
        idx = int(np.searchsorted(t_fine, 7.0))
        if 0 < idx < len(p_fine):
            t0, t1 = t_fine[idx - 1], t_fine[idx]
            p0, p1 = p_fine[idx - 1], p_fine[idx]
            if t1 > t0:
                frac = (7.0 - t0) / (t1 - t0)
                p_cross = p0 * (p1 / p0) ** frac  # log-linear interp
            else:
                p_cross = p_fine[idx]
            ax2.plot(p_cross, 7.0, "o", color="tab:red", ms=6)
            ax2.annotate(
                f"{name}: p≈{p_cross:.1e}",
                xy=(p_cross, 7.0),
                xytext=(p_cross * 2.5, 9 if name == "Mathis" else 11),
                fontsize=8,
                color="dimgray",
                arrowprops=dict(arrowstyle="->", color="dimgray", lw=0.5),
            )
    ax2.set_ylim(0, 20)
    ax2.set_xlabel("Packet loss probability  p")
    ax2.set_ylabel("Transfer time (seconds)")
    ax2.set_title(
        "Missing-closure fetch at S$_\\mathrm{EB\\text{-}tx}$=12 MB\n"
        "(2 MB over long-haul OWD=268 ms)"
    )
    ax2.grid(alpha=0.3, which="both")
    ax2.legend(loc="upper left")

    fig.tight_layout()
    path = os.path.join(BASE_PLOT_DIR, fname)
    fig.savefig(path, format="svg", bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")


# ---------------------------------------------------------------------------
# π₁ SENSITIVITY SWEEP
# ---------------------------------------------------------------------------

PI1_SWEEP_VALUES = (0.05, 0.10, 1.0 / 6.0, 0.30, 0.50)


def run_pi1_sensitivity(pi1_values=PI1_SWEEP_VALUES):
    """
    For each (network model × π₁) combination, run the full S_EB_tx sweep
    and collect P_validating, P_cert and the safety probability.

    Returns: { model_label: { pi1: [results_dict, ...], ... }, ... }
    """
    # Cache the active state so we can restore it on exit.
    saved_model = NETWORK_MODEL
    saved_pi1 = TX_CACHE_MISS_RATE

    out = {}
    for model in ("mathis", "cubic"):
        set_network_model(model)
        out[model] = {}
        for pi1 in pi1_values:
            set_cache_miss_rate(pi1)
            print(
                f"  [π₁ sensitivity] model={model:6s}  π₁={pi1:.4f}  ...",
                end="",
                flush=True,
            )
            out[model][pi1] = run_sweep()
            r12 = next(
                (r for r in out[model][pi1] if abs(r["s_eb_tx_kb"] - 12288) < 1), None
            )
            if r12:
                print(f"  P_cert@12MB = {r12['p_cert']:.4f}")
            else:
                print()

    set_network_model(saved_model)
    set_cache_miss_rate(saved_pi1)
    return out


def plot_pi1_sensitivity(sens, fname: str = "pi1_sensitivity.svg"):
    """
    Two-panel sensitivity plot: P_cert vs S_EB_tx for each π₁ value,
    one panel per network model.  Used to show how the quorum cliff
    shifts with the assumed cache miss rate.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 5.5), sharey=True)
    pi1_values = sorted(next(iter(sens.values())).keys())
    cmap = plt.cm.viridis(np.linspace(0.15, 0.85, len(pi1_values)))

    for ax, model in zip(axes, ("mathis", "cubic")):
        for pi1, color in zip(pi1_values, cmap):
            rs = sens[model][pi1]
            mbs = [r["s_eb_tx_kb"] / 1024 for r in rs]
            pcs = [r["p_cert"] for r in rs]
            tag = "1/6" if abs(pi1 - 1 / 6) < 1e-4 else f"{pi1:.2f}"
            lw = 2.2 if abs(pi1 - 1 / 6) < 1e-4 else 1.4
            ls = "-" if abs(pi1 - 1 / 6) < 1e-4 else "--"
            ax.plot(mbs, pcs, ls, color=color, lw=lw, label=f"π₁ = {tag}")
        ax.axhline(
            0.497,
            color="red",
            ls=":",
            lw=1,
            alpha=0.7,
            label="Praos P_cert cap ≈ 0.497",
        )
        ax.set_xlabel("S$_\\mathrm{EB\\text{-}tx}$  (MB)")
        ax.set_title(f"{model.upper()} model")
        ax.set_xlim(0, 12)
        ax.set_ylim(0, 0.55)
        ax.grid(alpha=0.3)
        ax.legend(loc="lower left", fontsize=8)
    axes[0].set_ylabel("P$_\\text{cert}$")
    fig.suptitle(
        "π₁ sensitivity: P$_\\text{cert}$ vs S$_\\mathrm{EB\\text{-}tx}$ "
        "at varying TxCache miss rates",
        fontsize=12,
    )
    fig.tight_layout()
    path = os.path.join(BASE_PLOT_DIR, fname)
    fig.savefig(path, format="svg", bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {path}")


def print_pi1_sensitivity_summary(sens):
    """Console table: P_cert @ S_EB_tx ∈ {1, 4, 8, 12 MB} for each model × π₁."""
    print("\n" + "=" * 78)
    print("π₁ SENSITIVITY — P_cert at selected S_EB_tx (per model)")
    print("=" * 78)
    sizes_kb = [1024, 4096, 8192, 12288]
    for model in ("mathis", "cubic"):
        print(f"\n[{model.upper()}]")
        header = f"  {'π₁':>6}  " + "  ".join(f"{s/1024:>4.0f}MB" for s in sizes_kb)
        print(header)
        print("  " + "-" * (len(header) - 2))
        for pi1, rs in sorted(sens[model].items()):
            cells = []
            for s_kb in sizes_kb:
                r = next((x for x in rs if abs(x["s_eb_tx_kb"] - s_kb) < 1), None)
                cells.append(f"{r['p_cert']:.3f}" if r else "  —")
            tag = "1/6" if abs(pi1 - 1 / 6) < 1e-4 else f"{pi1:.3f}"
            print(f"  {tag:>6}  " + "  ".join(f"{c:>6s}" for c in cells))


# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------


def run_standard_analysis(model_label: str):
    """
    Run the full standard analysis suite under the currently active network
    model (set via set_network_model).  All plots are saved to PLOT_DIR (which
    should already be set to plots/<model_label>/).  Returns a dict with the
    sweep results and key summary statistics.
    """
    print("\n[1/7] Computing reference (existing) model...")
    ref_cdf = run_reference()

    print("\n[2/7] Sweeping S_EB_tx values...")
    results = run_sweep()

    print("\n[3/7] Generating comparison plot...")
    plot_cdf_comparison(ref_cdf, results)

    print("\n[4/7] Generating EB-closure sweep plot...")
    plot_eb_closure_sweep(results)

    print("\n[5/7] Generating feasibility and certification plots...")
    plot_feasibility(results)
    plot_certification(results)

    print("\n[6/7] Generating outcome diagram and sensitivity analysis...")
    plot_outcome_diagram()
    sens = run_sensitivity_1hop_vs_blended()

    print("\n[7/7] Network-only diffusion analysis...")
    net_rows = run_network_diffusion()
    plot_network_diffusion(net_rows)
    print("\nNetwork-only feasibility (no reapply):")
    print(
        f"  {'S_EB_tx':>8}  {'1-hop P<=7s':>11}  {'blend-miss P<=7s':>16}  {'full-blend P<=14s':>17}"
    )
    for r in net_rows:
        print(
            f"  {r['s_kb']/1024:>8.2f}  {r['sw7_1hop']:>11.4f}  "
            f"{r['sw7_miss_blend']:>16.4f}  {r['sw14_full']:>17.4f}"
        )

    feasible = [r for r in results if r["p_cert"] >= 0.10 and r["sw14_cert"] >= 0.97]
    max_feasible_mb = max((r["s_eb_tx_kb"] / 1024 for r in feasible), default=0.0)

    r12 = min(results, key=lambda r: abs(r["s_eb_tx_kb"] - 12288))
    print("\n" + "=" * 70)
    print(f"SUMMARY [{model_label.upper()}] (S_EB_tx ≈ 12 MB):")
    print(f"  p_validating        = {r12['p_validating']:.4f}")
    print(f"  p_quorum            = {r12['p_quorum']:.4f}")
    print(f"  p_interrupted       = {r12['p_interrupted']:.4f}")
    print(f"  p_certified         = {r12['p_cert']:.4f}")
    print(f"  P(certRB <=14s)     = {r12['sw14_cert']:.4f}")
    print(f"  P(certified+safe)   = {r12['p_cert_and_safe']:.4f}")
    print(f"  Median combined: {r12['q50']:.2f}s")
    print(f"  75th pct:        {r12['q75']:.2f}s")
    print(f"  95th pct:        {r12['q95']:.2f}s")
    print(f"  99th pct:        {r12['q99']:.2f}s")
    print("\n  1-hop vs blended sensitivity (12MB):")
    print(f"    1-hop P(<=14s)   = {sens['1hop_sw14']:.4f}")
    print(f"    blended P(<=14s) = {sens['blended_sw14']:.4f}")

    print(f"\nFeasibility summary [{model_label.upper()}]:")
    for r in results:
        viable = " ✓" if r["p_cert_and_safe"] >= 0.20 else " ✗"
        print(
            f"  {r['s_eb_tx_kb']/1024:>7.3f} MB  p_cert={r['p_cert']:.4f}  "
            f"sw14_cert={r['sw14_cert']:.4f}  cert×safe={r['p_cert_and_safe']:.4f}{viable}"
        )

    print(
        f"\nMax feasible S_EB_tx (p_cert≥0.10 and sw14_cert≥0.97): "
        f"{max_feasible_mb:.3f} MB"
    )

    # Save JSON summary
    summary = []
    for r in results:
        summary.append(
            {
                k: float(v) if not isinstance(v, np.ndarray) else None
                for k, v in r.items()
                if k != "cdf_cert" and k != "cdf_tx" and k != "cdf_comb"
            }
        )
    summary_path = os.path.join(
        os.path.dirname(__file__), f"results_summary_{model_label}.json"
    )
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)

    print(f"\nAll {model_label} plots saved to {PLOT_DIR}")
    print(f"Results saved to results_summary_{model_label}.json")

    return dict(results=results, r12=r12, sens=sens, max_feasible_mb=max_feasible_mb)


def main():
    print("=" * 70)
    print("Improved Linear Leios DeltaQ Analysis (dual network model)")
    print(f"Grid: N={N}, DT={DT:.4f}s, T_MAX={T_MAX:.1f}s")
    print("=" * 70)

    # Always emit the network-model comparison plot (top-level, model-agnostic).
    print("\n>>> Generating network-model comparison plot (loss-rate sweep)...")
    plot_network_model_comparison()

    summaries = {}
    for model in ("mathis", "cubic"):
        print("\n" + "#" * 70)
        print(f"#  NETWORK MODEL: {model.upper()}")
        print("#" * 70)
        set_network_model(model)
        set_plot_subdir(model)
        summaries[model] = run_standard_analysis(model)

    # π₁ sensitivity sweep (across both models × multiple cache-miss rates).
    # Restores the default state on exit (mathis, π₁ = 1/6).
    print("\n" + "#" * 70)
    print("#  π₁ SENSITIVITY SWEEP")
    print("#" * 70)
    set_plot_subdir()  # back to base plots/ for the top-level sensitivity plot
    pi1_sens = run_pi1_sensitivity()
    plot_pi1_sensitivity(pi1_sens)
    print_pi1_sensitivity_summary(pi1_sens)

    # Cross-model headline table
    print("\n" + "=" * 70)
    print("HEADLINE COMPARISON  (S_EB_tx = 12 MB)")
    print("=" * 70)
    print(f"  {'Quantity':22s}  {'Mathis':>10s}  {'CUBIC':>10s}")
    for key, name in [
        ("p_validating", "P_validating"),
        ("p_quorum", "P_quorum"),
        ("p_cert", "P_cert"),
        ("sw14_cert", "P(certRB ≤14s)"),
        ("p_cert_and_safe", "P_cert × safe"),
    ]:
        m = summaries["mathis"]["r12"][key]
        c = summaries["cubic"]["r12"][key]
        print(f"  {name:22s}  {m:>10.4f}  {c:>10.4f}")
    print(
        f"  {'Max feasible S_EB_tx':22s}  "
        f"{summaries['mathis']['max_feasible_mb']:>7.1f} MB  "
        f"{summaries['cubic']['max_feasible_mb']:>7.1f} MB"
    )


if __name__ == "__main__":
    main()
