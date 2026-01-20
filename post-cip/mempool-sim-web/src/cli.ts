import { Command } from 'commander';
import { generateNetwork, addAdversaryNode } from './topology.js';
import { Simulation } from './simulation.js';
import { logger } from './logger.js'
import { OVERHEAD_B } from './link.js';

// Default configuration values
const DEFAULTS = {
  nodes: 50,
  degree: 6,
  block: 90000,          // 90 kB
  latency: 0.100,        // 100 ms
  bandwidth: 1250000,    // 10 Mb/s
  adversaries: 2,
  adversaryDegree: 18,   // 3x honest degree
  txCount: 250,
  txDuration: 20,        // seconds over which to inject txs
  txSizeMin: 200,        // minimum tx size in bytes
  txSizeMax: 16384,      // maximum tx size in bytes
  slotDuration: 20,      // seconds per block slot
  slots: 10,             // number of slots to simulate
  adversaryDelay: 0.002, // number of seconds needed to front-run a tx
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
  .option('--adversary-delay <seconds>', 'Time needed for adversary to front-run a transaction', String(DEFAULTS.adversaryDelay))
  .option('-t, --tx-count <number>', 'Number of transactions to inject', String(DEFAULTS.txCount))
  .option('--tx-duration <seconds>', 'Duration over which to inject transactions', String(DEFAULTS.txDuration))
  .option('--tx-size-min <bytes>', 'Minimum transaction size', String(DEFAULTS.txSizeMin))
  .option('--tx-size-max <bytes>', 'Maximum transaction size', String(DEFAULTS.txSizeMax))
  .option('--slot-duration <seconds>', 'Block slot duration in seconds', String(DEFAULTS.slotDuration))
  .option('-s, --slots <number>', 'Number of slots to simulate', String(DEFAULTS.slots))
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
  adversaryDelay: parseFloat(opts.adversaryDelay),
  txCount: parseInt(opts.txCount),
  txDuration: parseInt(opts.txDuration),
  txSizeMin: parseInt(opts.txSizeMin),
  txSizeMax: parseInt(opts.txSizeMax),
  slotDuration: parseInt(opts.slotDuration),
  slots: parseInt(opts.slots),
};

try {
  logger.info({
    ...config,
    ...{message_overhead_bytes: OVERHEAD_B},
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
      config.adversaryDelay,
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

  // Schedule rotating block production among honest nodes
  const honestNodes = Array.from({ length: config.nodes }, (_, i) => `H${i + 1}`);
  for (let slot = 0; slot < config.slots; slot++) {
    const producer = honestNodes[slot % honestNodes.length]!;
    sim.produceBlock(slot * config.slotDuration, producer, config.block);
  }

  logger.info({ slots: config.slots, slotDuration: config.slotDuration }, "block production scheduled");

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
  }, "mempool results");

  // Block statistics
  const blocks = sim.blocks;
  const totalHonestInBlocks = blocks.reduce((s, b) => s + b.honestCount, 0);
  const totalAdvInBlocks = blocks.reduce((s, b) => s + b.adversarialCount, 0);
  const totalInBlocks = totalHonestInBlocks + totalAdvInBlocks;

  logger.info({
    blocks_produced: blocks.length,
    txs_in_blocks: totalInBlocks,
    honest_tx_in_blocks: totalHonestInBlocks,
    adversarial_tx_in_blocks: totalAdvInBlocks,
    front_run_rate: totalInBlocks > 0 ? totalAdvInBlocks / totalInBlocks : 0,
    avg_block_fill_percent: blocks.length > 0
      ? blocks.reduce((s, b) => s + b.size_B, 0) / (blocks.length * config.block) * 100
      : 0
  }, "block statistics");

} catch (error) {
  logger.fatal({ error }, "simulation failed");
  console.log(`Fatal: ${error}`);
  process.exit(1);
}
