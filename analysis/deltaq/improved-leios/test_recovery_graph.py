"""Recovery-graph checks; run with unittest discovery."""

import unittest

import numpy as np
from scipy.sparse import csr_matrix

import analysis as A
import recovery_graph as G
import two_phase as T


class RecoveryGraphTests(unittest.TestCase):
    def test_peer_choices_have_no_duplicates_or_self_edges(self):
        graph = G.build_graph(np.ones(20) / 20, 5, np.random.default_rng(4))
        np.testing.assert_array_equal(graph.diagonal(), 0)
        np.testing.assert_array_equal(np.diff(graph.indptr), 5)
        self.assertTrue(np.all(graph.data == 1))

    def test_direction_long_paths_and_adversarial_transit(self):
        # 0 -> 1 -> 2 -> 3(holder); 4 -> 5(adversary) -> 3 is not usable.
        graph = csr_matrix(
            (np.ones(5), ([0, 1, 2, 4, 5], [1, 2, 3, 5, 3])), shape=(6, 6)
        )
        holders = np.array([False, False, False, True, False, False])
        honest = np.array([True, True, True, True, True, False])
        distances = G.holder_distances(graph, holders, honest)
        np.testing.assert_array_equal(distances[:4], [3, 2, 1, 0])
        self.assertTrue(np.isinf(distances[4]))
        self.assertTrue(np.isinf(distances[5]))

    def test_roles_reach_their_stake_and_leave_honest_receivers(self):
        stakes = G.node_stakes()
        self.assertEqual(len(stakes), G.N_NODES)
        self.assertAlmostEqual(stakes.sum(), 1)
        rng = np.random.default_rng(5)
        for f, a in G.STAKE_SPLITS:
            holders, honest = G.assign_roles(stakes, f, a, rng)
            self.assertGreaterEqual(stakes[holders].sum(), f)
            self.assertGreaterEqual(stakes[~honest].sum(), a)
            self.assertFalse(np.any(holders & ~honest))
            self.assertTrue(np.any(honest & ~holders))

    def test_one_hop_matches_closed_form(self):
        for f in (0.25, 0.5):
            paths = G.derive_paths(f, 5)
            # Distinct peers make one hop slightly more likely than the closed form.
            self.assertGreaterEqual(
                paths.weights[0], G.one_hop_closed_form(f, 5) - 0.005
            )
            self.assertLess(paths.weights[0], G.one_hop_closed_form(f, 5) + 0.01)

    def test_without_adversaries_every_receiver_is_reachable(self):
        paths = G.derive_paths(0.25, 5, 0.0)
        self.assertEqual(paths.unreachable, 0)
        self.assertEqual(paths.all_reachable, 1)
        self.assertAlmostEqual(sum(paths.weights), 1)

    def test_recovery_weights_exclude_unreachable_mass(self):
        paths = G.Paths(5, 0.25, 0.5, (0.6, 0.3), 0.1, 0.0, 10, 1)
        np.testing.assert_allclose(paths.recovery_weights(), (2 / 3, 1 / 3))

    def test_graph_recovery_does_not_change_phase_one(self):
        A.set_network_model("mathis")
        weights = G.derive_paths().recovery_weights()
        fixed = T.calculate(2000, 2000 * 40 / 260, recovery_hops=(0.5, 0.5))
        graph = T.calculate(2000, 2000 * 40 / 260, recovery_hops=weights)
        np.testing.assert_array_equal(graph.voter, fixed.voter)
        self.assertEqual(graph.log_pc, fixed.log_pc)
        self.assertEqual(graph.log_pc_active, fixed.log_pc_active)

    def test_no_peers_leaves_every_receiver_unreachable(self):
        paths = G.derive_paths(0.25, 0, 0.0, n_nodes=40, trials=4)
        self.assertEqual(sum(paths.weights), 0)
        self.assertEqual(paths.unreachable, 1)
        self.assertEqual(paths.all_reachable, 0)


if __name__ == "__main__":
    unittest.main()
