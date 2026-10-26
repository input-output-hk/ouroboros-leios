"""Stake-weighted fetch graphs for the phase-two recovery-hop distribution.

Each node requests data from a fixed set of distinct peers, chosen in
proportion to stake.  Holders are a uniformly random node set whose stake
first reaches a given fraction; optional adversaries neither serve nor
forward.  With stake-weighted peers, P(one hop) is close to 1 - (1 - f)^m
for holder stake f and m peers, so the sweep is indexed by f and m rather
than by a holder set conditioned on rare certification events.

Only the reachable hop law enters DeltaQ.  Unreachable receivers are a
property of a static topology without churn or peer replacement, and are
reported separately.
"""

from dataclasses import dataclass
from functools import lru_cache

import numpy as np
from scipy.sparse import csr_matrix, diags
from scipy.sparse.csgraph import dijkstra

import analysis as A


N_NODES = 2500
PEER_COUNTS = (5, 10, 20)
# (holder stake, adversarial stake); honest nonholders keep the remainder.
STAKE_SPLITS = ((.25, 0.), (.25, .25), (.25, .5), (.5, 0.), (.5, .25), (.75, 0.))
DEFAULT_PEERS = 5
DEFAULT_HOLDER_STAKE = .25
GRAPH_COUNT = 16
TRIALS = 256
SEED = 164


@dataclass(frozen=True)
class Paths:
    peers: int
    holder_stake: float
    adversary_stake: float
    weights: tuple
    unreachable: float
    all_reachable: float
    receivers: int
    trials: int

    def recovery_weights(self):
        """Hop law over reachable receivers, as used by the DeltaQ recovery CDF."""
        weights = np.asarray(self.weights)
        return tuple(weights / weights.sum())


def one_hop_closed_form(holder_stake, peers):
    """Peers drawn with replacement; sampling without replacement is slightly higher."""
    return 1 - (1 - holder_stake) ** peers


def node_stakes(n_nodes=N_NODES):
    # The distribution helper includes a negligible extra bin; a graph has
    # exactly n_nodes vertices, so omit the smallest bin here.
    stakes = np.sort(A._stake_distribution(n_nodes))[::-1][:n_nodes]
    return stakes / stakes.sum()


def build_graph(stakes, peers, rng):
    """i -> j means i can request from j; unique peers and no self edges."""
    n = len(stakes)
    if not 0 <= peers < n:
        raise ValueError("peer count must be between zero and population minus one")
    columns = np.empty((n, peers), dtype=int)
    for node in range(n):
        probabilities = np.array(stakes, dtype=float)
        probabilities[node] = 0
        probabilities /= probabilities.sum()
        columns[node] = rng.choice(n, peers, replace=False, p=probabilities)
    return csr_matrix((np.ones(n * peers), (np.repeat(np.arange(n), peers), columns.ravel())),
                      shape=(n, n))


def holder_distances(graph, holders, honest):
    """Fetch-path length from each node to its nearest holder.

    Adversarial nodes never serve or forward, so their edges are removed.
    Nodes without an honest route, and adversarial nodes, have infinite distance.
    """
    sources = np.flatnonzero(holders & honest)
    if not len(sources):
        return np.full(len(honest), np.inf)
    mask = diags(honest.astype(float))
    honest_graph = (mask @ graph @ mask).tocsr()
    honest_graph.eliminate_zeros()
    distances = dijkstra(honest_graph.T.tocsr(), directed=True, unweighted=True,
                         indices=sources, min_only=True)
    distances[~honest] = np.inf
    return distances


def assign_roles(stakes, holder_stake, adversary_stake, rng):
    """Random node order; holders, then adversaries, each take a prefix reaching their stake."""
    if holder_stake <= 0 or adversary_stake < 0 or holder_stake + adversary_stake >= 1:
        raise ValueError("holder and adversarial stake must leave honest nonholders")
    order = rng.permutation(len(stakes))
    cumulative = np.cumsum(stakes[order])
    holder_end = int(np.searchsorted(cumulative, holder_stake)) + 1
    adversary_end = holder_end
    if adversary_stake > 0:
        target = cumulative[holder_end - 1] + adversary_stake
        adversary_end = min(int(np.searchsorted(cumulative, target)) + 1, len(stakes) - 1)
    holders = np.zeros(len(stakes), dtype=bool)
    honest = np.ones(len(stakes), dtype=bool)
    holders[order[:holder_end]] = True
    honest[order[holder_end:adversary_end]] = False
    return holders, honest


@lru_cache(maxsize=None)
def graph_bank(peers, n_nodes=N_NODES, seed=SEED, count=GRAPH_COUNT):
    stakes = node_stakes(n_nodes)
    rng = np.random.default_rng((seed, peers))
    return tuple(build_graph(stakes, peers, rng) for _ in range(count)), stakes


@lru_cache(maxsize=None)
def derive_paths(holder_stake=DEFAULT_HOLDER_STAKE, peers=DEFAULT_PEERS, adversary_stake=0.,
                 n_nodes=N_NODES, seed=SEED, trials=TRIALS):
    """Pool shortest-path lengths over honest nonholders, not over stake."""
    graphs, stakes = graph_bank(peers, n_nodes, seed)
    rng = np.random.default_rng((seed, peers, round(1e4 * holder_stake), round(1e4 * adversary_stake)))
    counts = np.zeros(n_nodes + 1, dtype=np.int64)
    unreachable = receivers = complete = 0
    for trial in range(trials):
        holders, honest = assign_roles(stakes, holder_stake, adversary_stake, rng)
        distances = holder_distances(graphs[trial % len(graphs)], holders, honest)
        remaining = distances[honest & ~holders]
        finite = remaining[np.isfinite(remaining)].astype(int)
        counts += np.bincount(finite, minlength=n_nodes + 1)
        missed = np.count_nonzero(~np.isfinite(remaining))
        unreachable += missed
        receivers += len(remaining)
        complete += missed == 0
    last = max(1, int(np.flatnonzero(counts)[-1])) if counts.any() else 1
    return Paths(peers, holder_stake, adversary_stake, tuple(counts[1:last + 1] / receivers),
                 unreachable / receivers, complete / trials, receivers, trials)


def sweep():
    return [derive_paths(f, m, a) for m in PEER_COUNTS for f, a in STAKE_SPLITS]
