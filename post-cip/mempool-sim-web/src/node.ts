import { DirectedGraph } from 'graphology';
import { MemoryPool } from './mempool.js';
import type { Tx, TxId } from './types.js';
import { Link } from './link.js'
import { offerTx } from './events.js';
import { logger } from './logger.js';


export class Node {
  
  public readonly id: string;
  
  public readonly honest: boolean;
  
  private readonly mempool: MemoryPool<Tx>;
  
  private readonly backpressure: Tx[];

  private readonly offers: Map<TxId, Set<string>>;

  constructor(id: string, honest: boolean, mempool_B: number) {
    this.id = id;
    this.honest = honest;
    this.mempool = new MemoryPool<Tx>(mempool_B);
    this.backpressure = [];
    this.offers = new Map<TxId, Set<string>>();
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
      this.backpressure.pop();
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
    (this.offers.get(txId) ?? this.offers.set(txId, new Set()).get(txId)!).add(peer);
    this.fetchTxs(graph, now);
  }

  // Fetch txs from peers.
  private fetchTxs(graph: DirectedGraph<Node, Link>, now: number): void {
    if (this.backpressure.length > 0)
      return;
  }

}
