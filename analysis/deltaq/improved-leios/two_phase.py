"""Causal deadline-triggered closure recovery on analysis.py's time grid.

The joint node model is explicit.  Quorum probabilities use a seeded
permutation approximation to a non-negative binomial-mixture representation,
so conditioning preserves probability identities even in very small tails.
"""

from dataclasses import dataclass
from functools import lru_cache

import numpy as np
from scipy.special import gammaln, logsumexp, xlogy

import analysis as A


def sequential(left, right):
    """Sum positive grid times without losing one DT per convolution.

    analysis.cdf_sequential indexes the convolution from DT rather than 2*DT.
    Shift its result by one bin so deadline state and phase-two onset agree.
    """
    result = np.zeros_like(left)
    result[1:] = A.cdf_sequential(left, right)[:-1]
    return result


def node_completion(body, fetch, validate, recovery, reapply, deadline, stress=False):
    """Return (voter CDF, two-phase node-completion CDF).

    A node with all transaction data by deadline continues its original
    validation.  Otherwise it restarts the missing batch after both deadline
    and body arrival, then reapplies the whole closure.  Completed batch work
    is retained; partial transaction-transfer bytes are not credited.
    The component times are independent, with a shared body arrival for both
    phases.  Phase-two serving availability is an assumption conditional on C.
    In stress mode only already-validated nodes retain progress.  Every other
    node runs the supplied full-closure recovery law and reapplies, including
    nodes that had data but were still validating at the deadline.
    """
    tick = round(deadline / A.DT)
    if tick < 1 or tick >= len(body) or not np.isclose(tick * A.DT, deadline):
        raise ValueError("deadline must be an interior positive grid time")
    data = sequential(body, fetch)
    voter = sequential(data, validate)

    # Defective distribution: only nodes with complete data by deadline.
    known_data = data.copy()
    known_data[tick:] = data[tick - 1]
    continue_validation = sequential(known_data, validate)
    remaining_after_body = fetch
    if stress:
        continue_validation = voter.copy()
        continue_validation[tick:] = voter[tick - 1]
        remaining_after_body = sequential(fetch, validate)

    # Defective distribution of recovery start times max(B, deadline).
    start_mass = np.zeros_like(body)
    body_mass = np.maximum(A._to_pdf(body), 0)
    for index, mass in enumerate(body_mass):
        body_tick = index + 1
        available_ticks = tick - body_tick
        retained = remaining_after_body[available_ticks - 1] if available_ticks > 0 else 0.0
        start_mass[max(index, tick - 1)] += mass * (1 - retained)
    recover = sequential(sequential(np.cumsum(start_mass), recovery), reapply)
    completion = continue_validation + recover
    # Remove only roundoff; do not repair non-monotonic conditional curves.
    completion = np.clip(completion, 0, 1)
    completion[:tick] = voter[:tick]
    return voter, completion


QUORUM_SAMPLES = 50_000
QUORUM_SEED = 164


@lru_cache(maxsize=None)
def quorum_coefficients(n_nodes=2500, committee_size=900, tau=0.75, beta=0.0,
                        samples=QUORUM_SAMPLES, seed=QUORUM_SEED):
    """a[k] = P(a uniform k-seat subset reaches the stake threshold).

    Order seats uniformly at random and record the prefix length reaching
    quorum.  Its empirical CDF estimates a[k] for every k at once.  Then
    Q(p) = sum_k a[k] Binom(K,k,p).  This avoids direct rejection sampling
    of rare certification events and gives a probability-consistent Q.

    The active-adversary comparison is stylised: beta of committee weight
    votes deterministically, with each stochastic seat's weight scaled by
    1-beta.  It is not a particular adversarial allocation of real pools.
    """
    stakes = np.sort(A._stake_distribution(n_nodes))[::-1]
    weights = stakes[:min(committee_size, n_nodes)]
    threshold = tau * stakes.sum() - beta * weights.sum()
    K = len(weights)
    if threshold <= 0:
        return np.ones(K + 1)
    weights = (1 - beta) * weights
    if threshold > weights.sum():
        return np.zeros(K + 1)
    rng = np.random.default_rng(seed)
    counts = np.zeros(K + 1)
    for start in range(0, samples, 500):
        size = min(500, samples - start)
        permutations = rng.permuted(np.broadcast_to(weights, (size, K)), axis=1)
        crossing = np.argmax(np.cumsum(permutations, axis=1) >= threshold, axis=1) + 1
        counts += np.bincount(crossing, minlength=K + 1)
    return np.cumsum(counts) / samples


def log_quorum(p, n_nodes=2500, committee_size=900, tau=0.75, beta=0.0):
    coefficients = quorum_coefficients(n_nodes, committee_size, tau, beta)
    return log_quorum_from_coefficients(p, coefficients)


def log_quorum_from_coefficients(p, coefficients):
    """Evaluate the non-negative binomial polynomial without tail underflow."""
    K = len(coefficients) - 1
    k = np.flatnonzero(coefficients > 0)
    p = np.asarray(p, dtype=float)
    if len(k) == 0:
        return np.full_like(p, -np.inf)
    log_weights = (np.log(coefficients[k]) + gammaln(K + 1)
                   - gammaln(k + 1) - gammaln(K - k + 1))
    return np.minimum(logsumexp(log_weights + xlogy(k, p[..., None])
                               + xlogy(K - k, 1 - p[..., None]), axis=-1), 0)


def conditional_completion(voter, completion, deadline=7.0, n_nodes=2500,
                           committee_size=900, tau=0.75, beta=0.0):
    """Condition the explicit node model on the vote-deadline quorum.

    H(t_v,t) = F_V(min(t_v,t)): a node ready to vote is already complete.
    Unlike the old formula, the conditional voter probability is H/F_D.
    Node pairs are independent and identically distributed, including the
    counterfactual recovery times that are used only when C occurs.
    """
    tick = round(deadline / A.DT)
    p_vote = voter[tick - 1]
    log_pc = float(log_quorum(p_vote, n_nodes, committee_size, tau, beta))
    if not np.isfinite(log_pc):
        return log_pc, None
    joint = voter.copy()
    joint[tick:] = p_vote
    q = np.divide(joint, completion, out=np.zeros_like(joint), where=completion > 0)
    if np.any(q > 1 + 1e-10):
        raise ValueError("joint readiness exceeds node completion probability")
    q = np.clip(q, 0, 1)
    honest_nodes = round((1 - beta) * n_nodes)
    with np.errstate(divide="ignore"):
        log_result = honest_nodes * np.log(completion) + log_quorum(
            q, n_nodes, committee_size, tau, beta
        ) - log_pc
    if np.any(log_result > 1e-9):
        raise ValueError("conditional probability exceeds one")
    result = np.exp(np.minimum(log_result, 0))  # Roundoff only.
    if np.any(np.diff(result) < -1e-10):
        raise ValueError("conditional CDF must be non-decreasing without repair")
    return log_pc, result


@dataclass
class Result:
    voter: np.ndarray
    completion: np.ndarray
    log_pc: float
    honest: np.ndarray | None
    log_pc_active: float
    active: np.ndarray | None


def calculate(closure_kb, body_kb, deadline=7.0, recovery_hops=(0.5, 0.5), stress=False):
    body = A.cdf_fetch_eb_body(body_kb)
    fetch = A.cdf_fetch_missing_eb_closure(closure_kb, use_1hop=False)
    validate = A.cdf_process_eb_closure(closure_kb)
    if stress:
        # Full payload: do not multiply by the stationary missing fraction.
        recovery = A.cdf_choices([(weight, A.cdf_hops(hops, closure_kb))
                                 for hops, weight in enumerate(recovery_hops, 1) if weight > 0])
    else:
        recovery = A.cdf_fetch_missing_eb_closure(closure_kb, hop_weights=recovery_hops)
    reapply = A.cdf_process_eb_closure(closure_kb, reapply_only=True)
    voter, completion = node_completion(body, fetch, validate, recovery, reapply, deadline, stress=stress)
    log_pc, honest = conditional_completion(voter, completion, deadline)
    log_pc_active, active = conditional_completion(voter, completion, deadline, beta=0.25)
    return Result(voter, completion, log_pc, honest, log_pc_active, active)


def worst_case(closure_kb, body_kb, receivers, recovery_hops, deadline=7.0):
    """Return (node CDF, all-receiver CDF) for the late-release safety scenario.

    An adversary with stake approaching half the total votes on time and
    releases the EB so late that, at the deadline, only the minimal honest
    holders have it.  Certification is then certain, so nothing is
    conditioned.  Each of the remaining honest receivers fetches the body and
    then the full closure over the recovery-hop law, starting at the deadline,
    and validates in full.  Receivers complete independently.
    """
    tick = round(deadline / A.DT)
    if tick < 1 or tick >= A.N or not np.isclose(tick * A.DT, deadline):
        raise ValueError("deadline must be an interior positive grid time")
    def over_paths(payload_kb):
        return A.cdf_choices([(weight, A.cdf_hops(hops, payload_kb))
                              for hops, weight in enumerate(recovery_hops, 1) if weight > 0])
    node = sequential(sequential(over_paths(body_kb), over_paths(closure_kb)),
                      A.cdf_process_eb_closure(closure_kb))
    started = np.zeros_like(node)
    started[tick:] = node[:-tick]
    return started, started ** receivers
