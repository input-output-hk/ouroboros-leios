import { Command } from 'commander';
import { generateNetwork, addAdversaryNode } from './topology.js';
import { Simulation } from './simulation.js';
import { logger } from './logger.js'
import { OVERHEAD_B } from './link.js';

// Default configuration values
const DEFAULTS = {
  nodes: 50,
  degree: 6,
  block: 90000,        // 90 kB
  latency: 0.100,      // 100 ms
  bandwidth: 1250000,  // 10 Mb/s
  adversaries: 2,
  adversaryDegree: 18, // 3x honest degree
  txCount: 250,
  txDuration: 20,      // seconds over which to inject txs
  txSizeMin: 200,      // minimum tx size in bytes
  txSizeMax: 16384,    // maximum tx size in bytes
};

const program = new Command();

program
  .name('mempool-sim')
  .description('Memory pool simulation with adversarial front-running')
  .version('1.0.0')
  .option('-n, --nodes <number>', 'Number of honest nodes', String(DEFAULTS.nodes))
  .option('-d, --degree <number>', 'Node connectivity degree', String(DEFAULTS.degree))
  .option('-b, --block <bytes>', 'Block size in bytes', String(DEFAULTS.block))
  .option('-l, --latency <seconds>', 'Network latency in seconds', String(DEFAULTS.latency))
  .option('-w, --bandwidth <bps>', 'Bandwidth in bytes per second', String(DEFAULTS.bandwidth))
  .option('-a, --adversaries <number>', 'Number of adversary nodes', String(DEFAULTS.adversaries))
  .option('--adversary-degree <number>', 'Adversary connectivity degree', String(DEFAULTS.adversaryDegree))
  .option('-t, --tx-count <number>', 'Number of transactions to inject', String(DEFAULTS.txCount))
  .option('--tx-duration <seconds>', 'Duration over which to inject transactions', String(DEFAULTS.txDuration))
  .option('--tx-size-min <bytes>', 'Minimum transaction size', String(DEFAULTS.txSizeMin))
  .option('--tx-size-max <bytes>', 'Maximum transaction size', String(DEFAULTS.txSizeMax))
  .parse(process.argv);

const opts = program.opts();

// Parse configuration from CLI args
const config = {
  nodes: parseInt(opts.nodes),
  degree: parseInt(opts.degree),
  block: parseInt(opts.block),
  mempool: parseInt(opts.block) * 2, // mempool = 2x block size
  latency: parseFloat(opts.latency),
  bandwidth: parseInt(opts.bandwidth),
  adversaries: parseInt(opts.adversaries),
  adversaryDegree: parseInt(opts.adversaryDegree),
  txCount: parseInt(opts.txCount),
  txDuration: parseInt(opts.txDuration),
  txSizeMin: parseInt(opts.txSizeMin),
  txSizeMax: parseInt(opts.txSizeMax),
};

try {
  logger.info({
    nodes: { honest: config.nodes, adversarial: config.adversaries },
    degree: { honest: config.degree, adversarial: config.adversaryDegree },
    block_bytes: config.block,
    mempool_bytes: config.mempool,
    latency_s: config.latency,
    bandwidth_Bps: config.bandwidth,
    bandwidth_Mbps: config.bandwidth * 8 / 1000000,
    message_overhead_bytes: OVERHEAD_B,
    tx_count: config.txCount,
    tx_duration_s: config.txDuration,
    tx_size_range: { min: config.txSizeMin, max: config.txSizeMax },
  }, "configuration");

  // Generate honest node network
  const graph = generateNetwork(
    config.nodes,
    config.degree,
    config.mempool,
    config.latency,
    config.bandwidth
  );

  logger.info({ nodeCount: graph.order, edgeCount: graph.size }, "graph created");

  // Add adversary nodes
  for (let i = 0; i < config.adversaries; ++i) {
    addAdversaryNode(
      graph,
      "A" + (i + 1),
      config.adversaryDegree,
      config.adversaryDegree,
      config.mempool,
      config.latency,
      config.bandwidth
    );
  }

  // Log topology
  graph.forEachNode((node) => {
    const neighbors = graph.outNeighbors(node);
    logger.info({ node: node, downstream_peers: neighbors }, "topology");
  });

  // Create simulation
  const sim = new Simulation(graph);

  // Inject transactions at random honest nodes with random sizes
  for (let i = 0; i < config.txCount; ++i) {
    const txId = "T" + i;
    // Random honest node (H1 to H{nodes})
    const nodeIndex = Math.ceil(config.nodes * Math.random());
    const node = "H" + nodeIndex;
    // Random time within tx duration
    const time = Math.round(config.txDuration * Math.random());
    // Random size within configured range
    const size = config.txSizeMin + Math.floor(Math.random() * (config.txSizeMax - config.txSizeMin));

    sim.submitTx(time, node, {
      txId: txId,
      size_B: size,
      frontRuns: "",
    });
  }

  logger.info({ txCount: config.txCount, pendingEvents: sim.pendingEvents }, "transactions submitted");

  // Run the simulation
  sim.run();

  logger.info({ eventsProcessed: sim.eventsProcessed, finalTime: sim.currentTime }, "simulation complete");

  // Collect and report statistics
  let totalHonest = 0;
  let totalAdversarial = 0;
  let totalBytes = 0;

  graph.forEachNode((nodeId) => {
    const node = graph.getNodeAttributes(nodeId);
    node.logPartialState();
    const summary = node.mempoolSummary();
    totalHonest += summary.mempool_tx_count.honest;
    totalAdversarial += summary.mempool_tx_count.adversarial;
    totalBytes += summary.mempool_bytes;
  });

  const totalTxs = totalHonest + totalAdversarial;
  logger.info({
    total_txs_in_mempools: totalTxs,
    total_bytes_in_mempools: totalBytes,
    honest_tx_fraction: totalTxs > 0 ? totalHonest / totalTxs : 0,
    adversarial_tx_fraction: totalTxs > 0 ? totalAdversarial / totalTxs : 0,
    honest_tx_count: totalHonest,
    adversarial_tx_count: totalAdversarial,
  }, "simulation results");

} catch (error) {
  logger.fatal({ error }, "simulation failed");
  console.log(`Fatal: ${error}`);
  process.exit(1);
}
