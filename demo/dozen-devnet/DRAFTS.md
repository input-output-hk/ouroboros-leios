# Drafts — temporary, for editing across machines

Parked here so they can be pushed and pulled; **delete once posted**. None of
this is committed prose we want to keep in the repo long-term — the durable
record is `results/*/digest.md` and `BASELINE.md`.

| file | destination |
| --- | --- |
| `comment-911-draft.md` | comment on issue #911 (prototype high-throughput mempool) |
| `comment-845-draft.md` | comment on issue #845 (bottleneck for 200 TxkB/s) |
| `report-911-draft.md` | longer writeup behind the #911 comment |

Status: unposted. `gh` is authenticated as ch1bo on the bench machine, so
posting is `gh issue comment 911 --repo input-output-hk/ouroboros-leios -F
demo/dozen-devnet/comment-911-draft.md`.

Open points flagged in review, in case they need another pass:

- The long `report-911-draft.md` still has its §1–§4 body written against the
  older single-run data, before the paired bounded/unbounded runs. Its `## Thesis`
  section and the two comments are current; the body is not.
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
