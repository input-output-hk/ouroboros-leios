import { Command, Option } from 'commander';
import { generateNetwork, addAdversaryNode } from './topology.js';
import { Simulation } from './simulation.js';
import { logger, makeLogger } from './logger.js';
import { OVERHEAD_B } from './link.js';
import { computeFrontRunStats } from './stats.js';
const DEFAULTS = {
  nodes: 50,
  degree: 6,
  block: 90_000,
  latency: 0.100,
  bandwidth: 1_250_000,
  adversaries: 2,
  adversaryDegree: 18,
  txLoad_KBps: 100,
  txSize: 512,
  txDuration: 20,
  slotDuration: 20,
  slots: 10,
  adversaryDelay: 0.002,
  logLevel: 'info',
  logTarget: 'pino-pretty',
  ebSize: 10_000_000,
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
  .option('-t, --tx-load <kbps>', 'Transaction load in KB/s', String(DEFAULTS.txLoad_KBps))
  .option('--tx-size <bytes>', 'Uniform tx size in bytes', String(DEFAULTS.txSize))
  .option('--tx-duration <seconds>', 'Duration over which to inject txs', String(DEFAULTS.txDuration))
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
  .option('--eb-certification-rate <rate>', 'EB certification probability (0-1)', '0.5')
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
  txLoad_KBps: parseInt(opts.txLoad),
  txSize: parseInt(opts.txSize),
  txDuration: parseInt(opts.txDuration),
  slotDuration: parseInt(opts.slotDuration),
  slots: parseInt(opts.slots),
  logLevel: opts.logLevel as string,
  logTarget: opts.logTarget as string,
  eb: opts.eb === true,
  ebSize: parseInt(opts.ebSize),
  ebCertificationRate: parseFloat(opts.ebCertificationRate),
};

const mempool = config.eb
  ? 2 * (config.block + config.ebSize)
  : config.block * 2;

try {
  makeLogger(config.logLevel, config.logTarget);

  // Memory estimate
  const totalNodes = config.nodes + config.adversaries;
  const expectedTxCount = Math.ceil(config.txLoad_KBps * 1024 * config.txDuration / config.txSize);
  const bitmapBytesPerTx = Math.ceil(totalNodes / 32) * 4 * 3; // 3 bitmaps
  const estimatedMB = (expectedTxCount * 2 * bitmapBytesPerTx) / (1024 * 1024); // *2 for adversarial variants
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
  sim.ebCertificationRate = config.ebCertificationRate;

  // Register and inject transactions (byte-budget from KB/s load)
  const honestCount = config.nodes;
  const totalBytes = config.txLoad_KBps * 1024 * config.txDuration;
  let bytesInjected = 0;
  let txI = 0;
  const MAX_TXS = 50_000; // safety cap
  while (bytesInjected < totalBytes && txI < MAX_TXS) {
    const txId = `T${txI}`;
    const txIdx = sim.registry.register(txId, config.txSize, false, -1);
    const nodeIndex = Math.floor(Math.random() * honestCount);
    const time = config.txDuration * Math.random();
    sim.push({
      kind: 'SubmitTx',
      clock: time,
      nodeIdx: nodeIndex,
      txIdx,
    });
    bytesInjected += config.txSize;
    txI++;
  }

  logger.info({ txLoad_KBps: config.txLoad_KBps, txCount: txI, pendingEvents: sim.pendingEvents }, 'transactions submitted');

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
  const frontRunStats = computeFrontRunStats(
    reg.txs,
    blocks,
    sim.endorserBlocks,
    config.eb,
  );

  logger.info({
    blocks_produced: blocks.length,
    txs_in_blocks: frontRunStats.rbTotalTx,
    honest_tx_in_blocks: frontRunStats.rbHonestTx,
    adversarial_tx_in_blocks: frontRunStats.rbAdversarialTx,
    txs_in_chain: frontRunStats.totalTx,
    honest_tx_in_chain: frontRunStats.totalHonestTx,
    adversarial_tx_in_chain: frontRunStats.totalAdversarialTx,
    certified_eb_honest_tx: frontRunStats.certifiedEBHonestTx,
    certified_eb_adversarial_tx: frontRunStats.certifiedEBAdversarialTx,
    rb_front_run_rate: frontRunStats.rbFrontRunRate,
    total_front_run_rate: frontRunStats.totalFrontRunRate,
    front_run_rate: frontRunStats.totalFrontRunRate,
    avg_block_fill: blocks.length > 0
      ? blocks.reduce((s, b) => s + b.size_B, 0) / (blocks.length * config.block)
      : 0,
  }, 'block statistics');

  if (config.eb) {
    const ebs = sim.endorserBlocks;
    const certifiedCount = ebs.filter(eb => eb.certified).length;
    logger.info({
      endorser_blocks_produced: ebs.length,
      certified: certifiedCount,
      uncertified: ebs.length - certifiedCount,
      total_eb_txRefs: ebs.reduce((s, eb) => s + eb.txRefs.length, 0),
      certified_eb_honest_tx: frontRunStats.certifiedEBHonestTx,
      certified_eb_adversarial_tx: frontRunStats.certifiedEBAdversarialTx,
    }, 'endorser block statistics');
  }

  // Compute p_poison: for each honest tx with an adversarial variant,
  // what fraction of honest nodes have the adversarial version in mempool?
  // This is the metric Brian's analytical model predicts.
  const reg2 = sim.registry;
  const honestNodeIndices = sim.nodes
    .map((n, i) => n.honest ? i : -1)
    .filter(i => i >= 0);
  const honestNodeCount2 = honestNodeIndices.length;

  let pPoisonSum = 0;
  let pPoisonCount = 0;
  let reachSum = 0; // fraction of honest nodes that have EITHER version

  for (const tx of reg2.txs) {
    if (tx.isAdversarial) continue; // skip adversarial variants
    if (tx.adversarialVariant < 0) continue; // no adversarial variant created

    const advIdx = tx.adversarialVariant;
    let advInHonest = 0;
    let honestInHonest = 0;

    for (const ni of honestNodeIndices) {
      if (reg2.inMempool[advIdx]!.get(ni)) advInHonest++;
      if (reg2.inMempool[tx.idx]!.get(ni)) honestInHonest++;
    }

    const reached = advInHonest + honestInHonest;
    if (reached > 0) {
      pPoisonSum += advInHonest / reached;
      reachSum += reached / honestNodeCount2;
      pPoisonCount++;
    }
  }

  const pPoison = pPoisonCount > 0 ? pPoisonSum / pPoisonCount : 0;
  const avgReach = pPoisonCount > 0 ? reachSum / pPoisonCount : 0;
  const pAdv = config.adversaries / (config.nodes + config.adversaries);
  const lambda = Math.log(config.nodes + config.adversaries) / Math.log(config.degree);
  const theoryNoDelay = 1 - Math.pow(1 - pAdv, lambda - 1);
  const theoryDelay = pAdv;

  logger.info({
    p_poison: pPoison,
    p_poison_count: pPoisonCount,
    avg_reach: avgReach,
    p_adv: pAdv,
    lambda,
    theory_no_delay: theoryNoDelay,
    theory_delay: theoryDelay,
  }, 'poisoning analysis');

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
