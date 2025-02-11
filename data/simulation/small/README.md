# A scenario with 100 nodes
- Network is randomly generated with Cylindrical topology, and
  latencies simulating nodes spread across the globe.
- Uniform stake distribution.
- Each node has 10 upstream peers with 2000kBs links.
- Three topology files differing only in number of CPU cores.
- One config file for single-stage and one for send-recv voting to compare the two (also
    covering 5 and 20 stage lengths).
- The IB size and generation rate is tuned to utilize a third of 2000kBs, as
  Short-Leios targets.
- NOTE: Other size and timing parameters are mostly the defaults, which need to be updated.
