import json
import tempfile
import unittest
from pathlib import Path

from analyse import compute_metrics, parse_log_line


class AnalyseTest(unittest.TestCase):
    def test_parses_announcement_and_certification_events(self):
        announcement = parse_log_line(
            json.dumps(
                {
                    "at": "2026-07-30T12:00:00Z",
                    "ns": "Consensus.LeiosKernel.BlockAnnounced",
                    "data": {"blockHash": "announced", "slot": 10},
                }
            ),
            "pool1",
        )
        certification = parse_log_line(
            json.dumps(
                {
                    "at": "2026-07-30T12:00:01Z",
                    "ns": "Consensus.LeiosKernel.BlockCertified",
                    "data": {"blockHash": "certified", "slot": 10},
                }
            ),
            "pool2",
        )

        self.assertEqual(announcement.block_type, "announcement")
        self.assertEqual(certification.block_type, "certification")

    def test_metrics_track_event_nodes(self):
        lines = {
            "pool1.log": {
                "ns": "Consensus.LeiosKernel.BlockAnnounced",
                "data": {"blockHash": "a", "slot": 10},
            },
            "pool2.log": {
                "ns": "Consensus.LeiosKernel.BlockAnnounced",
                "data": {"blockHash": "b", "slot": 11},
            },
            "pool3.log": {
                "ns": "Consensus.LeiosKernel.BlockCertified",
                "data": {"blockHash": "c", "slot": 12},
            },
        }
        with tempfile.TemporaryDirectory() as directory:
            for filename, event in lines.items():
                event["at"] = "2026-07-30T12:00:00Z"
                Path(directory, filename).write_text(json.dumps(event) + "\n")

            metrics = compute_metrics(directory)

        self.assertEqual(metrics.leios_announcements_observed, 2)
        self.assertEqual(metrics.leios_certifications_observed, 1)
        self.assertEqual(metrics.announcement_nodes, {"pool1", "pool2"})
        self.assertEqual(metrics.certification_nodes, {"pool3"})


if __name__ == "__main__":
    unittest.main()
