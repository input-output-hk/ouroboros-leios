# tools/

Analysis scripts that reuse the `estimator` Python module. All scripts default
to the repo-root `inputs.yaml` if no config is supplied.

See [notes/parallel-chunking-mc-confidence.md](../notes/parallel-chunking-mc-confidence.md)
for guidance on when to trust the chunking outputs.

## `plot_chunking.py` — overlaid whole-file CDFs vs. number of parallel chunks

Visualizes the benefit of splitting a download into n parallel chunks. For
each n the script runs a Monte Carlo at the chunk size (`file_size_kb / n`)
and overlays the implied whole-file CDF `F_file(t) = F_chunk(t)^n` on one
SVG axes, so the leftward shift and tail collapse are visible at a glance.

```
tools/plot_chunking.py                            # defaults: ns=1,2,4,8,16,32, runs=50000
tools/plot_chunking.py --ns 1,4,16,64             # custom n set
tools/plot_chunking.py --scenario realistic       # link/n bandwidth per chunk
tools/plot_chunking.py custom.yaml -o myplot.svg  # use a different config / output
tools/plot_chunking.py --runs 10000               # faster but noisier tail
tools/plot_chunking.py --xmax 2                   # zoom x-axis to first 2 s
tools/plot_chunking.py --cdfmin 0.9               # zoom y-axis into top decile
tools/plot_chunking.py --ci                       # also emit one per-n CI plot
```

Options:

| Flag | Default | Meaning |
| --- | --- | --- |
| `config` (positional) | `inputs.yaml` | YAML config to load |
| `-o`, `--output` | `chunking.svg` | Output SVG path |
| `--ns` | `1,2,4,8,16,32` | Comma-separated n values to overlay |
| `--runs` | `50000` | Monte Carlo trials per n (tail stability) |
| `--scenario` | `optimistic` | `optimistic` = full link per chunk; `realistic` = link/n per chunk |
| `--xmax` | *(auto: slowest curve's P99 + 0.5 s)* | Cap the x-axis at this many seconds; curves continue off-frame |
| `--cdfmin` | `0` | Lower bound of the y-axis (cumulative probability) in `[0, 1)`. Use e.g. `0.9` to zoom into the top decile where curves cross P99 |
| `--ci` | off | Also write one companion SVG per n showing that curve with a pointwise bootstrap CI band. Main multi-curve plot is unchanged. Files are named `<stem>-n<NN>.svg`. |
| `--ci-runs` | `500` | Bootstrap resamples per x-position (used with `--ci`) |
| `--ci-alpha` | `0.05` | Significance level for CI band; `0.05` → 95 % CI |

Bootstrap caveat: the CI bands are **pointwise** (fixed t), so they may under-report
uncertainty in the *quantile* (read off horizontally at y=0.99) wherever the CDF
has a step. For a robust check, also run `tools/chunking_stability.py`.

Reading the plot: each colored curve is one n. The dashed grey line at
y = 0.99 marks the P99 level — drop a vertical eye-line from any curve's
intersection with it to read that n's whole-file P99 time. Legend in the
lower-right corner maps color to n.

## `chunking_stability.py` — Monte Carlo noise check across reseeds

Reruns the chunk-distribution simulation K times with different RNG seeds and
reports mean / std / range / CoV of the file-P99 estimate per n, plus a verdict
flag. Use it to know whether `--runs` is high enough for your config before
you trust the chunking plot.

```
tools/chunking_stability.py                      # defaults: 10 seeds × 50k runs
tools/chunking_stability.py --seeds 5 --runs 100000
tools/chunking_stability.py custom.yaml --ns 1,8,32
```

## `chunk_compare.py` — tabular sweep of file P99 vs. n

Same physics as `plot_chunking.py`, presented as a text table comparing the
baseline (n = 1) P99 against each chunked configuration's implied
whole-file P99. Reports both optimistic and realistic bandwidth models.

```
tools/chunk_compare.py                          # defaults
tools/chunk_compare.py custom.yaml              # use a different config
tools/chunk_compare.py --conditional            # also report P99 | ≥1 loss
```

The `--conditional` flag adds a companion table reporting
`P[≥1 loss]` and `P99 | ≥1 loss` for each n, both at the chunk level
and the whole-file level. Use it when marginal P99 collapses to the
no-loss minimum time (typical at low p ≤ 1e-5) — the conditional metric
is what chunking actually shrinks in that regime.
