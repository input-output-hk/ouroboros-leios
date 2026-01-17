import { generateNetwork, addAdversaryNode } from './topology.js';
import { submitTx, handleEvents } from './events.js'
import { logger } from './logger.js'
import { OVERHEAD_B  } from './link.js';

const NODES = 50;
const DEGREE = 6;
const BLOCK = 90000; // = 90 kB
const MEMPOOL = 2 * BLOCK;
const LATENCY = 0.100; // = 100 ms
const BANDWIDTH = 1250000; // = 10 Mb/s

const ADVERSARY_COUNT = 2;
const ADVERSARY_DEGREE = 3 * DEGREE;

const TX_COUNT = 250;
const TX_LAST_S = 20;

try {

  logger.info({
    nodes: {honest: NODES, adversarial: ADVERSARY_COUNT},
    degree: {honest: DEGREE, adversarial: ADVERSARY_DEGREE},
    block_bytes: BLOCK,
    mempool_bytes: MEMPOOL,
    latency_ms: LATENCY / 1000,
    bandwidth_Mbps: BANDWIDTH * 8 / 1000000,
    message_overhead_bytes: OVERHEAD_B,
    tx_count: TX_COUNT,
    last_tx_seconds: TX_LAST_S,
  }, "configuration");
  const graph = generateNetwork(NODES, DEGREE, MEMPOOL, LATENCY, BANDWIDTH);

  logger.info(graph, "graph");
  
  for (let i = 0; i < ADVERSARY_COUNT; ++i) {
    addAdversaryNode(graph, "A" + (i + 1), 3 * DEGREE, 3 * DEGREE, MEMPOOL, LATENCY, BANDWIDTH);
  }

  graph.forEachNode((node) => {
    const neighbors = graph.outNeighbors(node);
    logger.info({node: node, downstream_peers: neighbors}, "topology");
  });

  for (let i = 0; i < TX_COUNT; ++i) {
    const txId = "T" + i;
    const node = "H" + Math.ceil(NODES * Math.random());
    const time = Math.round(TX_LAST_S * Math.random());
    const size = Math.ceil(16384 * Math.random());
    submitTx(time, "H20", {
      txId: txId,
      size_B: 1500,
      frontRuns: "",
    });
  }

  handleEvents(graph);

  let honest: number = 0;
  let adversarial: number = 0;
  graph.forEachNode((nodeId) => {
    const node = graph.getNodeAttributes(nodeId);
    node.logPartialState();
    const summary = node.mempoolSummary().mempool_tx_count;
    honest += summary.honest;
    adversarial += summary.adversarial;
  });
  logger.info({
    honest_txs: honest / (honest + adversarial), 
    adversarial_txs: adversarial / (honest + adversarial)
  }, "mempool honesty");

} catch (error) {
  console.log(`Fatal: ${error}`);
}
