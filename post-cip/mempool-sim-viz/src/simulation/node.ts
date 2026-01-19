import { LRUCache } from 'lru-cache';
import { MemoryPool } from './mempool';
import { TXID_B, type Tx, type TxId, type Block } from './types';
import { Link } from './link';
import { logger } from './logger';
import type { Simulation } from './simulation';

const KNOWN_CACHE_SIZE = 10000;

export class Node {
  public readonly id: string;
  public readonly honest: boolean;
  private mempool: MemoryPool;
  private backpressure: Tx[];
  private offers: [TxId, string][];
  private known: LRUCache<TxId, boolean>;

  constructor(id: string, honest: boolean, mempool_B: number) {
    this.id = id;
    this.honest = honest;
    this.mempool = new MemoryPool(mempool_B);
    this.backpressure = [];
    this.offers = [];
    this.known = new LRUCache<TxId, boolean>({ max: KNOWN_CACHE_SIZE });
  }

  // Getters for visualization
  getMempoolContents(): Tx[] {
    return this.mempool.contents();
  }

  getMempoolFillPercent(): number {
    return this.mempool.getFillPercent();
  }

  getMempoolTxCount(): number {
    return this.mempool.count();
  }

  hasAdversarialTx(): boolean {
    return this.mempool.contents().some(tx => tx.frontRuns !== '');
  }

  removeConfirmedTxs(txIds: string[]): void {
    for (const txId of txIds) {
      this.mempool.remove(txId);
    }
  }

  public mempoolSummary(): { node: string; mempool_bytes: number; mempool_tx_count: { honest: number; adversarial: number } } {
    let honest: number = 0;
    let adversarial: number = 0;
    let bytes: number = 0;
    this.mempool.contents().forEach(tx => {
      bytes += tx.size_B;
      if (tx.frontRuns === "")
        honest += 1;
      else
        adversarial += 1;
    });
    return { node: this.id, mempool_bytes: bytes, mempool_tx_count: { honest, adversarial } };
  }

  public handleSubmitTx(sim: Simulation, now: number, tx: Tx): void {
    if (this.known.has(tx.txId)) {
      return;
    }

    const isHonestTx = tx.frontRuns === "";

    if (isHonestTx) {
      const advTxId = tx.txId + "adv";
      if (this.known.has(advTxId)) {
        this.known.set(tx.txId, true);
        logger.trace({ clock: now, node: this.id, txId: tx.txId }, "rejected honest tx (have adversarial version)");
        return;
      }
    } else {
      const originalTxId = tx.frontRuns;
      if (this.known.has(originalTxId)) {
        this.known.set(tx.txId, true);
        logger.trace({ clock: now, node: this.id, txId: tx.txId }, "rejected adversarial tx (have honest version)");
        return;
      }
    }

    this.known.set(tx.txId, true);

    if (isHonestTx && !this.honest) {
      const txAdv: Tx = {
        txId: tx.txId + "adv",
        size_B: tx.size_B,
        frontRuns: tx.txId,
      };
      this.known.set(txAdv.txId, true);
      tx = txAdv;
      logger.trace({ clock: now, node: this.id, originalTxId: tx.frontRuns, advTxId: tx.txId }, "front-running transaction");
    }

    this.backpressure.push(tx);
    logger.trace({ clock: now, node: this.id, txId: tx.txId }, "apply backpressure");
    this.fillMemoryPool(sim, now);
  }

  private fillMemoryPool(sim: Simulation, now: number): void {
    while (this.backpressure.length > 0) {
      const tx = this.backpressure[0];
      if (!tx) break;
      if (!this.mempool.contains(tx.txId)) {
        const okay = this.mempool.enqueue(tx, tx.size_B);
        if (!okay) break;
        logger.trace({ clock: now, node: this.id, txId: tx.txId }, "insert into memory pool");
        this.offerUpstream(sim, now, tx);
      }
      this.backpressure.shift();
      logger.trace({ clock: now, node: this.id, txId: tx.txId }, "remove backpressure");
    }
  }

  private offerUpstream(sim: Simulation, now: number, tx: Tx): void {
    const graph = sim.graph;
    graph.forEachInEdge(this.id, (_edge, link, peer) => {
      logger.trace({ clock: now, node: this.id, txId: tx.txId, upstreamPeer: peer }, "offer transaction");
      sim.offerTx(link.computeDelay(now, TXID_B), this.id, peer, tx.txId);
    });
  }

  public handleOfferTx(sim: Simulation, now: number, peer: string, txId: TxId): void {
    if (this.mempool.contains(txId)) return;
    this.offers.push([txId, peer]);
    this.fetchTxs(sim, now);
  }

  private fetchTxs(sim: Simulation, now: number): void {
    if (this.backpressure.length > 0) return;
    const graph = sim.graph;
    while (this.offers.length > 0) {
      const offer = this.offers.shift();
      const txId = offer![0];
      const peer = offer![1];
      this.offers = this.offers.filter(o => o[0] !== txId);
      logger.trace({ clock: now, node: this.id, peer: peer, txId: txId }, "request transaction");
      const link = this.getDownstreamLink(graph, peer);
      sim.requestTx(link.computeDelay(now, TXID_B), this.id, peer, txId);
    }
  }

  public handleRequestTx(sim: Simulation, now: number, peer: string, txId: TxId): void {
    const tx = this.mempool.get(txId);
    const graph = sim.graph;
    if (tx) {
      logger.trace({ clock: now, node: this.id, peer: peer, tx: tx }, "send transaction");
      const link = this.getUpstreamLink(graph, peer);
      sim.sendTx(link.computeDelay(now, tx.size_B), this.id, peer, tx);
    } else {
      logger.warn({ clock: now, node: this.id, peer: peer, txId: txId }, "cannot send transaction");
    }
  }

  public handleSendTx(sim: Simulation, now: number, peer: string, tx: Tx): void {
    logger.trace({ clock: now, node: this.id, peer: peer, tx: tx }, "receive transaction");
    this.handleSubmitTx(sim, now, tx);
  }

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
      timestamp: now,
      transactions: txs,
      size_B: size,
      honestCount: honest,
      adversarialCount: adversarial
    };

    sim.recordBlock(block);
  }

  private getDownstreamLink(graph: Simulation['graph'], peer: string): Link {
    const link = graph.edge(this.id, peer);
    if (!link) {
      logger.fatal({ source: peer, target: this.id }, "downstream link not found");
      throw new Error("downstream link not found");
    }
    return graph.getEdgeAttributes(link);
  }

  private getUpstreamLink(graph: Simulation['graph'], peer: string): Link {
    const link = graph.edge(peer, this.id);
    if (!link) {
      logger.fatal({ source: peer, target: this.id }, "upstream link not found");
      throw new Error("upstream link not found");
    }
    return graph.getEdgeAttributes(link);
  }
}
