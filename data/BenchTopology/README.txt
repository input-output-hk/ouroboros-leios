

--- topology-dense-52.json ---
The topology specification for our benchmarking cluster.
We use 3 different AWS regions. Each node is connected to 6 other nodes:
* 4 in the same region
* 1 in each other region

The topology is static (i.e., no dynamic P2P), which is a requirement for reproducible
diffusion metrics in benchmarks.

All nodes named 'node-*' are block producers for the benchmark.
The 'explorer' node is an administrative node so to speak, which we use for
monitoring an ongoing cluster run. You can probably disregard that one for a
Leios simulation.


--- topology-dense-52-by-region.pdf ---
A rendered graph grouping nodes by AWS region.
(The AWS region labels 'US' and 'AP' appear swapped in the PDF, apologies).


--- topology-dense-52-as-torus.pdf ---
A rendered graph illustrating the torus-like nature of the topology.


--- example-node-configs/ ---
A directory containing the actual 'topology.json' files for each node used to
configure a benchmarking run on the cluster.

The node-to-ip-mapping.txt is added only as a human-readable lookup for the IPs used,
in case you need that for clarification.

Note that the IP addresses have been anonymized in a manner that preserves subnet relationships.

--- latency.sqlite3 ---
The latency matrix for a deployed cluster.

On each node, a series of pings is performed to each of its peers specified in the topology.
This also implies that each of the edges is measured in two directions.
Each series of pings is performed three times, with varying package sizes (min, max, and default size).
All results end up in the database's 'ping' table, which looks like this (example):

> sqlite> .mode table
> sqlite> select * from ping limit 1;
> +--------+--------+------+------+---------------+-------------+
> | source |  dest  | size | time | source_region | dest_region |
> +--------+--------+------+------+---------------+-------------+
> | node-0 | node-1 | 24   | 90.3 | EU            | US          |
> +--------+--------+------+------+---------------+-------------+ 


Example queries:

> SELECT source, dest, AVG(time) FROM ping WHERE size=64 AND source<dest GROUP BY source, dest
Most likely what you want for the simulation: the avg ping RTT in ms, at default packet size, for
all edges defined in the topology - disregarding bi-directional measurements, which might
differ very very slightly.
(i.e. ping from 'node-0' to 'node-1' shown, but from 'node-1' to 'node-0' not shown)

> SELECT source, dest, source_region, dest_region, AVG(time) FROM ping WHERE size=64 GROUP BY source, dest
Same as above, but more detailed and including bi-directional measurements.
Result includes the nodes' AWS regions, so you can gauge how "expensive" the transition between
certain regions was at the time of measurement.
