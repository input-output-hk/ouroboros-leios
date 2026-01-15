import { DirectedGraph } from 'graphology';
import { MemoryPool } from './mempool.js';
import type { Tx, TxId } from './types.js';
import { Link } from './link.js'
import { offerTx } from './events.js';


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
  handleSubmitTx(graph: DirectedGraph<Node, Link>, now: number, tx: Tx): void {
    this.backpressure.push(tx);
    this.fillMemoryPool(graph, now);
  };

  // Move transactions from the client to the memory pool until it is full.
  fillMemoryPool(graph: DirectedGraph<Node, Link>, now: number): void {
    while (this.backpressure.length > 0) {
      const tx = this.backpressure[0];
      if (!tx)
        break;
      const okay = this.mempool.enqueue(tx, tx?.size_B)
      if (!okay)
        break;
      this.backpressure.pop();
      this.offerUpstream(graph, now, tx);
    }
  }

  // Offer a transaction to upstream peers.
  offerUpstream (graph: DirectedGraph<Node, Link>, now: number, tx: Tx): void {
    graph.forEachInEdge(this.id, (_link, link, peer, _node) => {
      offerTx(link.computeDelay(now, tx.size_B), this.id, peer, tx.id)
    });
  }

  // Receive an offer of a TxId.
  handleOfferTx(graph: DirectedGraph<Node, Link>, now: number, peer: string, txId: TxId): void {
    (this.offers.get(txId) ?? this.offers.set(txId, new Set()).get(txId)!).add(peer);
  }

}
