import { Command, Option } from 'commander';
import { generateNetwork, addAdversaryNode } from './topology.js';
import { Simulation } from './simulation.js';
import { logger, makeLogger } from './logger.js';
import { OVERHEAD_B } from './link.js';
import type { TxCacheMode } from './types.js';

const DEFAULTS = {
  nodes: 50,
  degree: 6,
  block: 90_000,
  latency: 0.100,
  bandwidth: 1_250_000,
  adversaries: 2,
  adversaryDegree: 18,
  txCount: 250,
  txDuration: 20,
  txSizeMin: 200,
  txSizeMax: 16_384,
  slotDuration: 20,
  slots: 10,
  adversaryDelay: 0.002,
  logLevel: 'info',
  logTarget: 'pino-pretty',
  ebSize: 10_000_000,
  txCacheMode: 'mempool' as TxCacheMode,
};

const program = new Command();

program
  .name('mempool-sim')
  .description('Scaled bitmap memory pool simulator (Praos + Leios)')
  .version('2.0.0')
  .option('-n, --nodes <number>', 'Number of honest nodes', String(DEFAULTS.nodes))
  .option('-d, --degree <number>', 'Node connectivity degree', String(DEFAULTS.degree))
  .option('-b, --block <bytes>', 'Block size in bytes', String(DEFAULTS.block))
  .option('-l, --latency <seconds>', 'Network latency in seconds', String(DEFAULTS.latency))
  .option('-w, --bandwidth <bps>', 'Bandwidth in bytes per second', String(DEFAULTS.bandwidth))
  .option('-a, --adversaries <number>', 'Number of adversary nodes', String(DEFAULTS.adversaries))
  .option('--adversary-degree <number>', 'Adversary connectivity degree', String(DEFAULTS.adversaryDegree))
  .option('--adversary-delay <seconds>', 'Adversary front-run delay', String(DEFAULTS.adversaryDelay))
  .option('-t, --tx-count <number>', 'Number of transactions to inject', String(DEFAULTS.txCount))
  .option('--tx-duration <seconds>', 'Duration over which to inject txs', String(DEFAULTS.txDuration))
  .option('--tx-size-min <bytes>', 'Min tx size', String(DEFAULTS.txSizeMin))
  .option('--tx-size-max <bytes>', 'Max tx size', String(DEFAULTS.txSizeMax))
  .option('--slot-duration <seconds>', 'Block slot duration', String(DEFAULTS.slotDuration))
  .option('-s, --slots <number>', 'Number of slots to simulate', String(DEFAULTS.slots))
  .addOption(
    new Option('--log-level <level>', 'Log level')
      .choices(['fatal', 'error', 'warn', 'info', 'debug', 'trace'])
      .default(DEFAULTS.logLevel)
  )
  .addOption(
    new Option('--log-target <target>', 'Log target')
      .choices(['pino-pretty', 'pino/file'])
      .default(DEFAULTS.logTarget)
  )
  .option('--eb', 'Enable endorser blocks (Leios)', false)
  .option('--eb-size <bytes>', 'Endorser block size in bytes', String(DEFAULTS.ebSize))
  .addOption(
    new Option('--tx-cache-mode <mode>', 'Where EB-fetched txs go')
      .choices(['cache-only', 'mempool', 'both'])
      .default(DEFAULTS.txCacheMode)
  )
  .parse(process.argv);

const opts = program.opts();

const config = {
  nodes: parseInt(opts.nodes),
  degree: parseInt(opts.degree),
  block: parseInt(opts.block),
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
  logLevel: opts.logLevel as string,
  logTarget: opts.logTarget as string,
  eb: opts.eb === true,
  ebSize: parseInt(opts.ebSize),
  txCacheMode: opts.txCacheMode as TxCacheMode,
};

const mempool = config.eb
  ? 2 * (config.block + config.ebSize)
  : config.block * 2;

try {
  makeLogger(config.logLevel, config.logTarget);

  // Memory estimate
  const totalNodes = config.nodes + config.adversaries;
  const bitmapBytesPerTx = Math.ceil(totalNodes / 32) * 4 * 3; // 3 bitmaps
  const estimatedMB = (config.txCount * 2 * bitmapBytesPerTx) / (1024 * 1024); // *2 for adversarial variants
  logger.info({
    ...config,
    mempool_B: mempool,
    overhead_B: OVERHEAD_B,
    estimated_bitmap_MB: estimatedMB.toFixed(1),
  }, 'configuration');

  // Generate topology
  const { nodes, links } = generateNetwork(
    config.nodes,
    config.degree,
    mempool,
    config.latency,
    config.bandwidth,
  );

  logger.debug({ nodeCount: nodes.length, edgeCount: links.size }, 'graph created');

  // Add adversaries
  for (let i = 0; i < config.adversaries; i++) {
    addAdversaryNode(
      nodes,
      links,
      config.adversaryDegree,
      config.adversaryDegree,
      config.adversaryDelay,
      mempool,
      config.latency,
      config.bandwidth,
    );
  }

  // Create simulation
  const sim = new Simulation(nodes, links);
  sim.ebEnabled = config.eb;
  sim.ebSize_B = config.ebSize;
  sim.txCacheMode = config.txCacheMode;

  // Register and inject transactions
  const honestCount = config.nodes;
  for (let i = 0; i < config.txCount; i++) {
    const txId = `T${i}`;
    const size = config.txSizeMin + Math.floor(Math.random() * (config.txSizeMax - config.txSizeMin));
    const txIdx = sim.registry.register(txId, size, false, -1);
    const nodeIndex = Math.floor(Math.random() * honestCount); // honest nodes are 0..honestCount-1
    const time = Math.round(config.txDuration * Math.random());
    sim.push({
      kind: 'SubmitTx',
      clock: time,
      nodeIdx: nodeIndex,
      txIdx,
    });
  }

  logger.info({ txCount: config.txCount, pendingEvents: sim.pendingEvents }, 'transactions submitted');

  // Schedule block production (matching original: slot index as clock, probabilistic)
  for (let slot = 0; slot < config.slots; slot++) {
    if (Math.random() * config.slotDuration >= 1) continue;
    const producerIdx = Math.floor(Math.random() * honestCount);
    sim.push({
      kind: 'ProduceBlock',
      clock: slot,
      producerIdx,
      blockSize_B: config.block,
    });
  }

  logger.info({ slots: config.slots, slotDuration: config.slotDuration }, 'block production scheduled');

  // Run
  const t0 = performance.now();
  sim.run();
  const elapsed = ((performance.now() - t0) / 1000).toFixed(2);

  logger.info({
    eventsProcessed: sim.eventsProcessed,
    finalTime: sim.currentTime,
    wallTime_s: elapsed,
  }, 'simulation complete');

  // Statistics
  const reg = sim.registry;
  let honestInMempools = 0;
  let advInMempools = 0;
  for (const tx of reg.txs) {
    const count = reg.inMempool[tx.idx]!.count();
    if (count > 0) {
      if (tx.isAdversarial) advInMempools++;
      else honestInMempools++;
    }
  }

  const totalInMempools = honestInMempools + advInMempools;
  logger.info({
    unique_txs_in_mempools: totalInMempools,
    honest_unique: honestInMempools,
    adversarial_unique: advInMempools,
    honest_fraction: totalInMempools > 0 ? honestInMempools / totalInMempools : 0,
    adversarial_fraction: totalInMempools > 0 ? advInMempools / totalInMempools : 0,
  }, 'mempool statistics');

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
    avg_block_fill: blocks.length > 0
      ? blocks.reduce((s, b) => s + b.size_B, 0) / (blocks.length * config.block)
      : 0,
  }, 'block statistics');

  if (config.eb) {
    const ebs = sim.endorserBlocks;
    logger.info({
      endorser_blocks_produced: ebs.length,
      total_eb_txRefs: ebs.reduce((s, eb) => s + eb.txRefs.length, 0),
    }, 'endorser block statistics');
  }

  // Memory usage
  const mem = process.memoryUsage();
  logger.info({
    rss_MB: (mem.rss / 1024 / 1024).toFixed(1),
    heapUsed_MB: (mem.heapUsed / 1024 / 1024).toFixed(1),
    heapTotal_MB: (mem.heapTotal / 1024 / 1024).toFixed(1),
  }, 'memory usage');

} catch (error) {
  logger.fatal({ error }, 'simulation failed');
  process.exit(1);
}
