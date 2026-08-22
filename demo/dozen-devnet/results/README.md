# Results

One directory per run. **Digests, not raw logs** — a two-generator run writes
1.7 GB of node logs in 20 minutes, and twice now a run has filled the disk and
taken all twelve nodes down mid-write. What survives is what was extracted:

| file | what it is |
| --- | --- |
| `digest.md` | per-node mempool add path (rate, gap distribution, stall share, peak depth), per-generator submission stats, run summary |
| `sampler.tsv` | 10 s samples from `scripts/sample.py`: slot, on-chain bytes/s, forge counters (RB/EB blocks, txs, bytes), mean EB fill, bytes-per-tx, per-node mempool depth and N2N ingest |
| `provenance.txt` | resolved path, version and sha256 of each binary, plus the run's settings — the only durable way to tell a nix-store node from a `cabal` build, since both report the same git rev |

The narrative and the conclusions live in [`../BASELINE.md`](../BASELINE.md);
these are the numbers behind it.

`scripts/sample.py` writes `sampler.tsv`; `scripts/digest.py` writes `digest.md`.
Between them they cover the two things that cannot be recovered later: the
sub-scrape-interval add gaps, and the forge-loop call tree.

Extract a digest before deleting a run's logs — `digest.md` shows the shape, and
the gap distribution in particular cannot be recovered from metrics, because the
1 s scrape interval cannot see a 0.4 ms per-add latency.
