# Praos block diffusion comparison with benchmark cluster.

We compare the diffusion latency of blocks of the `praos-diffusion`
simulation with measurements obtained from a benchmark cluster of 52
nodes spread across different regions. More specifically we compare
adoption time latency, i.e. time since slot start.

Results:
 * times from the simulation are generally slower, with a delta within
   10% when comparing averages for differernt percentiles.
 * very close timings when running with 1 vs. 8 cores, seems to align
   with how the measured cpu load rarely goes above 100%.
 * same goes for halving bandwidth, but times are noticeably slower
   with 1/100th bandwidth: confirms simulation results are sensitive
   to bandwidth, but not so much we need precise measurements.

A possible source of the slower timings is the simulation's lack of
optimizations such as header pipelining.

## Reproduction steps and data
We read parameters and topology from:
* config.yaml -- reuses the shared leios configuration format
* topology.yaml -- derived from data/BenchTopology
the source of the values are documented within.

We ran the simulation for 48000s, matching the analyzed time for the cluster.
```
$ cabal run ols -- sim praos-diffusion --seed 42 -l config.yaml -t topology.yaml --output-seconds=48000 --output-file=...
```

The average adoption times for different stake (equivalently node) percentile.

| stake% | adoption, s | delta% |
|--------|-------------|--------|
| 50     | 0.70426     | 3      |
| 80     | 1.13167     | 8      |
| 90     | 1.17377     | 10     |
| 92     | 1.18070     | 10     |
| 94     | 1.18712     | 10     |
| 96     | 1.19231     | 10     |
| 98     | 1.19632     | 8      |
| 100    | 1.23190     | 6      |

See `./graphs` for plots of the distributions.

## Controls
* Average (body) block fetch duration is 0.3777s, close but around 6%
  slower than measured.

  Note: Serialization time with the chosen body size and bandwidth is
  around 0.0007s, so the majority of block fetch duration time should
  be due to latencies (at least 3 messages, one roundtrip) plus
  effects from congestion window and multiplexing. Could be
  interesting to look deeper into the network logs and verify the
  impacts of each factor mentioned above.

* See `controls/` for number of cores and bandwidth variations topologies.

### Bandwidth/100 topology
* average block fetch duration: 0.4242s
* average latencies:
  ```
  {
    "0.5": 0.8800847489361321,
    "0.8": 1.306744727663091,
    "0.9": 1.4174759312714138,
    "0.92": 1.4239426748281825,
    "0.94": 1.4300382719071536,
    "0.96": 1.4351744106528943,
    "0.98": 1.440421551546462,
    "1.0": 1.5425114879725337
  }
  ```
