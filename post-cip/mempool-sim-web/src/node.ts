import { LRUCache } from 'lru-cache';
import { MemoryPool } from './mempool.js';
import { TXID_B, type Tx, type TxId, type Block } from './types.js';
import { Link } from './link.js'
import { logger } from './logger.js';
import type { Simulation } from './simulation.js';
import { PeerManager } from './peer-manager.js';

// Maximum entries in the known txId cache per node.
// Prevents unbounded memory growth during long simulations.
const KNOWN_CACHE_SIZE = 10000;

export class Node {

  // The node ID, which is also stored in the graph object.
  public readonly id: string;

  // Whether the node is honest.
  public readonly honest: boolean;

  // The delay (in seconds) to front-run a transaction.
  public readonly frontrunDelay: number;

  // The memory pool.
  private mempool: MemoryPool;

  // Transactions backed up on the client, awaiting entry to the memory pool.
  private backpressure: Tx[];

  // Offers of transactions from upstream peers.
  private offers: [TxId, string][];

  // LRU cache of known transaction IDs (for duplicate detection).
  // Bounded to prevent memory growth in long-running simulations.
  private known: LRUCache<TxId, boolean>;

  // P2P peer manager (null if P2P is disabled)
  private peerManager: PeerManager | null = null;

  constructor(id: string, honest: boolean, frontrunDelay: number, mempool_B: number) {
    this.id = id;
    this.honest = honest;
    this.frontrunDelay = frontrunDelay;
    this.mempool = new MemoryPool(mempool_B);
    this.backpressure = [];
    this.offers = [];
    this.known = new LRUCache<TxId, boolean>({ max: KNOWN_CACHE_SIZE });
  }

  // Visualization getters
  getTransactions(): Tx[] {
    return this.mempool.contents();
  }

  getFillPercent(): number {
    return this.mempool.getFillPercent();
  }

  hasAdversarialTx(): boolean {
    return this.mempool.contents().some(tx => tx.frontRuns !== '');
  }

  removeConfirmedTxs(sim: Simulation, now: number, txIds: string[]): void {
    for (const txId of txIds) {
      this.mempool.remove(txId);
    }
    this.backpressure = this.backpressure.filter(tx => !txIds.includes(tx.txId));
    this.offers = this.offers.filter(txId => !txIds.includes(txId[0]!));
    this.fillMemoryPool(sim, now);
  }

  // Reset node state for simulation restart (keeps topology)
  reset(mempool_B: number): void {
    this.mempool = new MemoryPool(mempool_B);
    this.backpressure = [];
    this.offers = [];
    this.known.clear();
    if (this.peerManager) {
      this.peerManager.reset();
    }
  }

  // Initialize P2P peer selection for this node
  initializeP2P(targetActivePeers: number, churnProbability: number, upstreamPeers: string[]): void {
    this.peerManager = new PeerManager(this.id, targetActivePeers, churnProbability);
    this.peerManager.initialize(upstreamPeers);
  }

  // Handle P2P churn event
  handlePeerChurn(sim: Simulation, now: number): void {
    if (this.peerManager) {
      this.peerManager.churn();
      // Schedule next churn event
      const config = sim.p2pConfig;
      if (config && config.enabled) {
        sim.schedulePeerChurn(now + config.churnInterval, this.id);
      }
    }
  }

  // Get the peer manager (for testing/debugging)
  getPeerManager(): PeerManager | null {
    return this.peerManager;
  }

  // Log the partial state of the node.
  public logPartialState(): void {
    logger.debug({
      node: this.id,
      honest: this.honest,
      mempool: {
        summary: this.mempoolSummary(),
        contents: this.mempool.contents()
      }
    }, "node partial state");
  }

  // Summarize the memory pool.
  public mempoolSummary(): any {
    let honest: number = 0;
    let adversarial: number = 0;
    let bytes: number = 0;
    this.mempool.contents().forEach(tx => {
      bytes += tx.size_B;
      if (tx.frontRuns == "")
        honest += 1;
      else
        adversarial += 1;
    });
    return {node: this.id, mempool_bytes: bytes, mempool_tx_count: {honest, adversarial}};
  }

  // Log the memory pool summarization.
  public logMempoolSummary(): void {
    logger.debug(this.mempoolSummary(), "mempool summary");
  }

  // Submit a transaction to a node, applying backpressure if needed.
  // Handles duplicate detection for both honest and adversarial (front-run) transactions.
  public handleSubmitTx(sim: Simulation, now: number, tx: Tx): void {
    // Already seen this exact transaction
    if (this.known.has(tx.txId)) {
      logger.trace({clock: now, node: this.id, txId: tx.txId}, "transaction already known");
      return;
    }

    const isHonestTx = tx.frontRuns === "";

    if (isHonestTx) {
      // This is an honest transaction - check if we already have its adversarial version
      const advTxId = tx.txId + "adv";
      if (this.known.has(advTxId)) {
        // We already have the front-run version, reject the original
        this.known.set(tx.txId, true); // Mark as seen to prevent future processing
        logger.trace({clock: now, node: this.id, txId: tx.txId}, "rejected honest tx (have adversarial version)");
        return;
      }
    } else {
      // This is an adversarial (front-run) transaction - check if we have the original
      const originalTxId = tx.frontRuns;
      if (this.known.has(originalTxId)) {
        // We already have the honest version, reject the front-run
        this.known.set(tx.txId, true); // Mark as seen to prevent future processing
        logger.trace({clock: now, node: this.id, txId: tx.txId}, "rejected adversarial tx (have honest version)");
        return;
      }
    }

    // Mark this transaction as known
    this.known.set(tx.txId, true);

    // If this node is adversarial and receives an honest tx, front-run it
    if (isHonestTx && !this.honest) {
      const txAdv: Tx = {
        txId: tx.txId + "adv",
        size_B: tx.size_B,
        frontRuns: tx.txId,
      };
      // Also mark the adversarial version as known
      this.known.set(txAdv.txId, true);
      tx = txAdv;
      logger.trace({clock: now, node: this.id, originalTxId: tx.frontRuns, advTxId: tx.txId}, "front-running transaction");
    }

    this.backpressure.push(tx);
    logger.trace({clock: now, node: this.id, txId: tx.txId}, "apply backpressure");
    this.fillMemoryPool(sim, now);
  }

  // Move transactions from the client to the memory pool until it is full.
  private fillMemoryPool(sim: Simulation, now: number): void {
    while (this.backpressure.length > 0) {
      const tx = this.backpressure[0];
      if (!tx) {
        logger.fatal({clock: now, node: this.id}, "null transaction in backpressure");
        throw new Error("null transaction in backpressure");
      }
      if (!this.mempool.contains(tx.txId)) {
        const okay = this.mempool.enqueue(tx, tx.size_B)
        if (!okay) {
        //logger.trace({clock: now, node: this.id, tx: tx, mempool: this.mempool}, "cannot insert into full memory pool");
          break;
        } else {
          let delay = this.honest ? 0 : this.frontrunDelay;
          this.backpressure.shift();
          logger.trace({clock: now, node: this.id, txId: tx.txId}, "insert into memory pool");
          this.offerUpstream(sim, now + delay, tx);
        }
      } else {
        this.backpressure.shift();
        logger.trace({clock: now, node: this.id, tx: tx}, "tx already in memory pool");
      }
    }
  }

  // Offer a transaction to upstream peers.
  private offerUpstream(sim: Simulation, now: number, tx: Tx): void {
    const graph = sim.graph;

    if (this.peerManager) {
      // P2P mode: only offer to active upstream peers
      const activePeers = this.peerManager.getActivePeers();
      for (const peer of activePeers) {
        const edgeKey = graph.edge(peer, this.id);
        if (edgeKey) {
          const link = graph.getEdgeAttributes(edgeKey);
          logger.trace({clock: now, node: this.id, txId: tx.txId, upstreamPeer: peer, p2p: true}, "offer transaction");
          sim.offerTx(link.computeDelay(now, TXID_B), this.id, peer, tx.txId);
        }
      }
    } else {
      // Static mode: existing behavior (all in-edges)
      graph.forEachInEdge(this.id, (_edge, link, peer, _node) => {
        logger.trace({clock: now, node: this.id, txId: tx.txId, upstreamPeer: peer}, "offer transaction");
        sim.offerTx(link.computeDelay(now, TXID_B), this.id, peer, tx.txId)
      });
    }
  }

  // Receive an offer of a TxId.
  public handleOfferTx(sim: Simulation, now: number, peer: string, txId: TxId): void {
    if (this.mempool.contains(txId))
      return;
    this.offers.push([txId, peer]);
    this.fetchTxs(sim, now);
  }

  // Fetch txs from peers.
  private fetchTxs(sim: Simulation, now: number): void {
    if (this.backpressure.length > 0)
      return;
    const graph = sim.graph;
    while (this.offers.length > 0) {
      const offer = this.offers.shift();
      const txId = offer![0];
      // FIXME: Should we always take the first offer? or a random one?
      const peer = offer![1];
      this.offers = this.offers.filter(offer => offer[0] != txId);
      logger.trace({clock: now, node: this.id, peer: peer, txId: txId}, "request transaction");
      const link = this.getDownstreamLink(graph, peer);
      sim.requestTx(link.computeDelay(now, TXID_B), this.id, peer, txId);
    }
  }

  // Receive a request for a Tx.
  public handleRequestTx(sim: Simulation, now: number, peer: string, txId: TxId): void {
    const tx = this.mempool.get(txId);
    const graph = sim.graph;
    if (tx) {
      logger.trace({clock: now, node: this.id, peer: peer, tx: tx}, "send transaction");
      const link = this.getUpstreamLink(graph, peer);
      sim.sendTx(link.computeDelay(now, tx.size_B), this.id, peer, tx);
    } else {
      logger.warn({clock: now, node: this.id, peer: peer, txId: txId}, "cannot send transaction");
    }
  }

  // Receive a Tx.
  public handleSendTx(sim: Simulation, now: number, peer: string, tx: Tx): void {
    logger.trace({clock: now, node: this.id, peer: peer, tx: tx}, "receive transaction");
    this.handleSubmitTx(sim, now, tx);
  }

  // Produce a block by collecting transactions from the mempool.
  public handleProduceBlock(sim: Simulation, now: number, blockSize_B: number): void {
    const txs: Tx[] = [];
    let size = 0;
    let honest = 0;
    let adversarial = 0;

    while (size < blockSize_B) {
      const tx = this.mempool.peek();
      if (!tx || size + tx.size_B > blockSize_B) break;
      this.mempool.dequeue();
      txs.push(tx);
      size += tx.size_B;
      if (tx.frontRuns === "") {
        honest++;
      } else {
        adversarial++;
      }
    }

    const block: Block = {
      blockId: `B${sim.blocks.length}`,
      producer: this.id,
      clock: now,
      transactions: txs,
      size_B: size,
      honestCount: honest,
      adversarialCount: adversarial
    };

    sim.diffuseBlock(block);
  }

  // Lookup a downstream link by its peer name.
  private getDownstreamLink(graph: Simulation['graph'], peer: string): Link {
    const link = graph.edge(this.id, peer)
    if (!link) {
      logger.fatal({source: peer, target: this.id}, "downstream link not found");
      throw new Error("downstream link not found");
    }
    return graph.getEdgeAttributes(link)
  }

  // Lookup an upstream link by its peer name.
  private getUpstreamLink(graph: Simulation['graph'], peer: string): Link {
    const link = graph.edge(peer, this.id)
    if (!link) {
      logger.fatal({source: peer, target: this.id}, "upstream link not found");
      throw new Error("upstream link not found");
    }
    return graph.getEdgeAttributes(link)
  }

}
