# Drafts — temporary, for editing across machines

Parked here so they can be pushed and pulled; **delete once posted**. None of
this is committed prose we want to keep in the repo long-term — the durable
record is `results/*/digest.md` and `BASELINE.md`.

| file | destination |
| --- | --- |
| `comment-911.md` | comment on issue #911 (prototype high-throughput mempool) — **consolidated, ready for review** |
| `comment-845.md` | comment on issue #845 (bottleneck for 200 TxkB/s) |

`comment-911.md` supersedes the two earlier #911 drafts, which are deleted. It
folds the long writeup into the comment and cites the existing screenshots by
permalink where they corroborate: issuecomment-5370677604 (baseline: "remote
mempools can't keep up, throughput often at 0 despite capacity left") and
issuecomment-5372640504 (double buffering: "mempools coming more in sync", and
the third injection point giving less of a bump).

`issue-911-mempool-congestion.md` in this directory is the **older** writeup: no
thesis section, and its §4 still carries a ceiling model that later measurements
disproved (it assumed any later block can certify an EB, when only the
succeeding one can). Superseded by `comment-911.md`; delete or rewrite rather
than treating it as the record.

Status: unposted. `gh` is authenticated as ch1bo on the bench machine, so
posting is `gh issue comment 911 --repo input-output-hk/ouroboros-leios -F
demo/dozen-devnet/comment-911-draft.md`.

Open points flagged in review, in case they need another pass:

- Inclusion (~52–53%) is treated as near a structural ceiling, since
  `e^(-gap x f)` gives 61% at the current `minCertificationGap` of 10 and 50% at
  the CIP's 14. Both comments were corrected to stop reading the gap to 100% as
  headroom.
- Dropped a "certification 78% -> 99%" claim from both: it came from counting
  distinct `rbHash` in `Certified` traces, and `rbHash` there is the *announcing*
  header, so the ratio does not mean what the label suggested. `tooLate` 78 -> 0
  is the defensible number.
- `minCertificationGap` is 10 in `LeiosDemoTypes.hs` against 14 in the CIP
  recommendations. All measurements are against the code's value. Framed as a
  parameterization gap rather than a spec-divergence claim.
