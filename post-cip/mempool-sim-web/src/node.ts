import { DirectedGraph } from 'graphology';
import { MemoryPool } from './mempool.js';
import type { Tx, TxId } from './types.js';
import { Link } from './link.js'
import { offerTx, requestTx } from './events.js';
import { logger } from './logger.js';


export class Node {
  
  // The node ID, which is also stored in the graph object.
  public readonly id: string;
  
  // Whether the node is honest.
  public readonly honest: boolean;
  
  // The memory pool.
  private mempool: MemoryPool;
  
  // Transactions backup up on the client, awaiting entry to the memory poool.
  private backpressure: Tx[];

  // Offers of transactions from upstream peers.
  private offers: [TxId, string][];

  constructor(id: string, honest: boolean, mempool_B: number) {
    this.id = id;
    this.honest = honest;
    this.mempool = new MemoryPool(mempool_B);
    this.backpressure = [];
    this.offers = [];
  }

  // Submit a transaction to a node, applying backpressure if needed.
  public handleSubmitTx(graph: DirectedGraph<Node, Link>, now: number, tx: Tx): void {
    this.backpressure.push(tx);
    logger.info({clock: now, node: this.id, txId: tx.id}, "Apply backpressure");
    this.fillMemoryPool(graph, now);
  };

  // Move transactions from the client to the memory pool until it is full.
  private fillMemoryPool(graph: DirectedGraph<Node, Link>, now: number): void {
    while (this.backpressure.length > 0) {
      const tx = this.backpressure[0];
      if (!tx)
        break;
      const okay = this.mempool.enqueue(tx, tx?.size_B)
      if (!okay)
        break;
      this.backpressure.shift();
      logger.info({clock: now, node: this.id, txId: tx.id}, "Remove backpressure");
      logger.info({clock: now, node: this.id, txId: tx.id}, "Insert into memory pool");
      this.offerUpstream(graph, now, tx);
    }
  }

  // Offer a transaction to upstream peers.
  private offerUpstream (graph: DirectedGraph<Node, Link>, now: number, tx: Tx): void {
    graph.forEachInEdge(this.id, (_link, link, peer, _node) => {
      logger.info({clock: now, node: this.id, txId: tx.id, upstreamPeer: peer}, "Offer transaction");
      offerTx(link.computeDelay(now, tx.size_B), this.id, peer, tx.id)
    });
  }

  // Receive an offer of a TxId.
  public handleOfferTx(graph: DirectedGraph<Node, Link>, now: number, peer: string, txId: TxId): void {
    if (this.mempool.contains(txId))
      return;
    this.offers.push([txId, peer]);
    this.fetchTxs(graph, now);
  }

  // Fetch txs from peers.
  private fetchTxs(graph: DirectedGraph<Node, Link>, now: number): void {
    if (this.backpressure.length > 0)
      return;
    while (this.offers.length > 0) {
      const offer = this.offers.shift();
      const txId = offer![0];
      // FIXME: Should we always take the first offer?
      const peer = offer![1];
      this.offers = this.offers.filter(offer => offer[0] != txId);
      logger.info({clock: now, node: this.id, peer: peer, txId: txId}, "Request transaction");
      requestTx(now, this.id, peer, txId);
    }
  }

}
