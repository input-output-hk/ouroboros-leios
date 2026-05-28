# tools/

Analysis scripts that reuse the `estimator` Python module. All scripts default
to the repo-root `inputs.yaml` if no config is supplied.

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

Reading the plot: each colored curve is one n. The dashed grey line at
y = 0.99 marks the P99 level — drop a vertical eye-line from any curve's
intersection with it to read that n's whole-file P99 time. Legend in the
lower-right corner maps color to n.

## `chunk_compare.py` — tabular sweep of file P99 vs. n

Same physics as `plot_chunking.py`, presented as a text table comparing the
baseline (n = 1) P99 against each chunked configuration's implied
whole-file P99. Reports both optimistic and realistic bandwidth models.

```
tools/chunk_compare.py                  # defaults
tools/chunk_compare.py custom.yaml      # use a different config
```
