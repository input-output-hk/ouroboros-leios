"""Run with: python3 -m unittest discover -s analysis/deltaq/improved-leios -p test_two_phase.py"""

import itertools
import unittest
from unittest.mock import patch

import numpy as np

import analysis as A
import two_phase as T


class TwoPhaseTests(unittest.TestCase):
    def deterministic(self, body, fetch, validate, recovery, reapply, deadline):
        return T.node_completion(*(A.cdf_wait(t) for t in
                                  (body, fetch, validate, recovery, reapply)), deadline)

    def test_sum_preserves_elapsed_time(self):
        np.testing.assert_allclose(T.sequential(A.cdf_wait(1), A.cdf_wait(2)), A.cdf_wait(3), atol=1e-12)

    def test_ready_node_keeps_its_completion(self):
        voter, completion = self.deterministic(1, 1, 1, 5, 1, 4)
        np.testing.assert_allclose(voter, A.cdf_wait(3), atol=1e-12)
        np.testing.assert_allclose(completion, voter, atol=1e-12)

    def test_complete_data_keeps_validation_in_progress(self):
        _, completion = self.deterministic(1, 2, 2, 5, 1, 4)
        np.testing.assert_allclose(completion, A.cdf_wait(5), atol=1e-12)

    def test_missing_batch_recovery_starts_at_deadline(self):
        voter, completion = self.deterministic(1, 5, 1, 1, .5, 3)
        np.testing.assert_allclose(voter, A.cdf_wait(7), atol=1e-12)
        np.testing.assert_allclose(completion, A.cdf_wait(4.5), atol=1e-12)
        self.assertAlmostEqual(A.success_within(completion, 3), 0, places=12)

    def test_recovery_waits_for_late_body(self):
        _, completion = self.deterministic(4, 2, 1, 1, .5, 3)
        np.testing.assert_allclose(completion, A.cdf_wait(5.5), atol=1e-12)

    def test_no_recovery_change_to_vote_readiness(self):
        for model in ("mathis", "cubic"):
            A.set_network_model(model)
            slow = T.calculate(2000, 2000 * 40 / 260, recovery_hops=(0, 1))
            fast = T.calculate(2000, 2000 * 40 / 260, recovery_hops=(1,))
            np.testing.assert_array_equal(slow.voter, fast.voter)
            self.assertEqual(slow.log_pc, fast.log_pc)
            np.testing.assert_array_equal(slow.completion[:700], slow.voter[:700])
            self.assertTrue(np.all(fast.completion >= slow.completion - 1e-12))

    def test_node_distributions_match_enumerated_histories(self):
        choices = ((1, 4), (1, 3), (.5, 2), (.5, 1), (.25, .75))
        laws = [A.cdf_choice(.5, A.cdf_wait(a), A.cdf_wait(b)) for a, b in choices]
        voter, completion = T.node_completion(*laws, deadline=3)
        expected_vote = np.zeros(A.N)
        expected_complete = np.zeros(A.N)
        for body, fetch, validate, recovery, reapply in itertools.product(*choices):
            data_time = body + fetch
            vote_time = data_time + validate
            complete_time = vote_time if data_time <= 3 else max(body, 3) + recovery + reapply
            expected_vote += A.cdf_wait(vote_time) / 32
            expected_complete += A.cdf_wait(complete_time) / 32
        np.testing.assert_allclose(voter, expected_vote, atol=1e-12)
        np.testing.assert_allclose(completion, expected_complete, atol=1e-12)

    def test_conditional_formula_matches_enumerated_node_states(self):
        # Two equal-weight committee seats; one vote suffices; three nodes.
        coefficients = np.array([0., 1., 1.])
        voter = A.cdf_choice(.4, A.cdf_wait(1), A.cdf_wait(5))
        completion = A.cdf_choices([(.4, A.cdf_wait(1)), (.3, A.cdf_wait(3)), (.3, A.cdf_wait(4))])
        def exact_quorum(p, *args):
            return T.log_quorum_from_coefficients(p, coefficients)
        with patch.object(T, "log_quorum", exact_quorum):
            log_pc, cdf = T.conditional_completion(voter, completion, deadline=2, n_nodes=3)
        self.assertAlmostEqual(np.exp(log_pc), 1 - .6**2)
        for t in (1, 2, 3, 4, 5):
            probability = 0.
            for states in itertools.product(range(3), repeat=3):
                if not any(s == 0 for s in states[:2]):
                    continue
                if all((1, 3, 4)[s] <= t for s in states):
                    probability += np.prod([(.4, .3, .3)[s] for s in states])
            self.assertAlmostEqual(A.success_within(cdf, t), probability / (1 - .6**2))

    def test_log_quorum_survives_underflow(self):
        log_p = T.log_quorum_from_coefficients(1e-200, np.array([0., 0., 1.]))
        self.assertTrue(np.isfinite(log_p))
        self.assertAlmostEqual(log_p, 2 * np.log(1e-200))

    def test_insufficient_committee_stake_is_impossible(self):
        with patch.object(A, "_stake_distribution", return_value=np.array([.4, .3, .2, .1])):
            coefficients = T.quorum_coefficients(4, 1, .75, 0., 100, 57)
        np.testing.assert_array_equal(coefficients, [0, 0])
        self.assertEqual(T.log_quorum_from_coefficients(1., coefficients), -np.inf)

    def test_permutation_coefficients_match_small_exact_subsets(self):
        stakes = np.array([.4, .3, .2, .1])
        with patch.object(A, "_stake_distribution", return_value=stakes):
            coefficients = T.quorum_coefficients(4, 4, .6, 0., 20_000, 991)
        exact = []
        for k in range(5):
            subsets = list(itertools.combinations(stakes, k))
            exact.append(sum(sum(s) >= .6 for s in subsets) / len(subsets))
        np.testing.assert_allclose(coefficients, exact, atol=.015)
        self.assertTrue(np.all(np.diff(coefficients) >= 0))


if __name__ == "__main__":
    unittest.main()
