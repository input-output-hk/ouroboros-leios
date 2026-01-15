import { generateNetwork, addAdversaryNode } from './topology.js';
import { submitTx, handleEvents } from './events.js'
import type { TxId, Tx } from './types.js'
import { logger } from './logger.js'

const NODES = 50;
const DEGREE = 6;
const BLOCK = 90000;
const MEMPOOL = 2 * BLOCK;
const LATENCY = 0.100; // = 100 ms
const BANDWIDTH = 1250000; // = 10 Mb/s

const ADVERSARY_COUNT = 2;
const ADVERSARY_DEGREE = 3 * DEGREE;

try {

  logger.info({
    nodes: {honest: NODES, adversarial: ADVERSARY_COUNT},
    degree: {honest: DEGREE, adversarial: ADVERSARY_DEGREE},
    block_bytes: BLOCK,
    mempool_bytes: MEMPOOL,
    latency_ms: LATENCY / 1000,
    bandwidth_Mbps: BANDWIDTH * 8 / 1000000,
  }, "Configuration");
  const graph = generateNetwork(NODES, DEGREE, MEMPOOL, LATENCY, BANDWIDTH);

  logger.info({nodes: graph.order, links: graph.size}, "Graph");
  
  for (let i = 0; i < ADVERSARY_COUNT; ++i) {
    addAdversaryNode(graph, "A" + (i + 1), 3 * DEGREE, 3 * DEGREE, MEMPOOL, LATENCY, BANDWIDTH);
  }

  graph.forEachNode((node) => {
    const neighbors = graph.outboundNeighbors(node);
    logger.info({node: node, downstream_peers: neighbors}, "Topology");
  });

  submitTx(1.05, "H20", {
    id: "T1",
    size_B: 1500,
    honest: true,
  });

  submitTx(0, "H10", {
    id: "T2",
    size_B: 1500,
    honest: true,
  });

  handleEvents(graph);

} catch (error) {
  logger.fatal(error, "Error");
}
