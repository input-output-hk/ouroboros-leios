import { DirectedGraph } from 'graphology';
import { MemoryPool } from './mempool.js';
import { TXID_B, type Tx, type TxId } from './types.js';
import { Link } from './link.js'
import { offerTx, requestTx, sendTx, submitTx } from './events.js';
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

  // Transactions already known.
  private known: Set<TxId>;

  constructor(id: string, honest: boolean, mempool_B: number) {
    this.id = id;
    this.honest = honest;
    this.mempool = new MemoryPool(mempool_B);
    this.backpressure = [];
    this.offers = [];
    this.known = new Set<TxId>();
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
  public handleSubmitTx(graph: DirectedGraph<Node, Link>, now: number, tx: Tx): void {
    const txAdv = {
      txId: tx.txId + "adv",
      size_B: tx.size_B,
      frontRuns: tx.txId,
    };
    // FIXME: Check this logic.
    if (this.known.has(tx.txId) || this.known.has(tx.frontRuns) || this.known.has(txAdv.txId))
      return;
    this.known.add(tx.txId);
    if (tx.frontRuns == "" && !this.honest) {
      tx = txAdv;
      this.known.add(tx.txId);
    }
    this.backpressure.push(tx);
    logger.trace({clock: now, node: this.id, txId: tx.txId}, "apply backpressure");
    this.fillMemoryPool(graph, now);
  };

  // Move transactions from the client to the memory pool until it is full.
  private fillMemoryPool(graph: DirectedGraph<Node, Link>, now: number): void {
    while (this.backpressure.length > 0) {
      const tx = this.backpressure[0];
      if (!tx)
        break;
      if (!this.mempool.contains(tx.txId)) {
        const okay = this.mempool.enqueue(tx, tx?.size_B)
        if (!okay)
          break;
        logger.trace({clock: now, node: this.id, txId: tx.txId}, "insert into memory pool");
        this.offerUpstream(graph, now, tx);
      }
      this.backpressure.shift();
      logger.trace({clock: now, node: this.id, txId: tx.txId}, "remove backpressure");
    }
  }

  // Offer a transaction to upstream peers.
  private offerUpstream (graph: DirectedGraph<Node, Link>, now: number, tx: Tx): void {
    graph.forEachInEdge(this.id, (_edge, link, peer, _node) => {
      logger.trace({clock: now, node: this.id, txId: tx.txId, upstreamPeer: peer}, "offer transaction");
      offerTx(link.computeDelay(now, TXID_B), this.id, peer, tx.txId)
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
      // FIXME: Should we always take the first offer? or a random one?
      const peer = offer![1];
      this.offers = this.offers.filter(offer => offer[0] != txId);
      logger.trace({clock: now, node: this.id, peer: peer, txId: txId}, "request transaction");
      const link = this.getDownstreamLink(graph, peer);
      requestTx(link.computeDelay(now, TXID_B), this.id, peer, txId);
    }
  }

  // Receive a request for a Tx.
  public handleRequestTx(graph: DirectedGraph<Node, Link>, now: number, peer: string, txId: TxId): void {
    const tx = this.mempool.get(txId);
    if (tx) {
      logger.trace({clock: now, node: this.id, peer: peer, tx: tx}, "send transaction");
      const link = this.getUpstreamLink(graph, peer);
      sendTx(link.computeDelay(now, tx.size_B), this.id, peer, tx);
    } else{
      logger.warn({clock: now, node: this.id, peer: peer, txId: txId}, "cannnot send transaction");
    }
  }

  // Receive a Tx.
  public handleSendTx(graph: DirectedGraph<Node, Link>, now: number, peer: string, tx: Tx): void {
    logger.trace({clock: now, node: this.id, peer: peer, tx: tx}, "receive transaction");
    this.handleSubmitTx(graph, now, tx);
  }

  // Lookup a downstream link by its peer name.
  private getDownstreamLink(graph: DirectedGraph<Node, Link>, peer: string): Link {
      const link = graph.edge(this.id, peer)
      if (!link) {
        logger.fatal({source: peer, target: this.id}, "downstream link not found");
        throw new Error("downstream link not found");
      }
      return graph.getEdgeAttributes(link)
  }

  // Lookup an upstream link by its peer name.
  private getUpstreamLink(graph: DirectedGraph<Node, Link>, peer: string): Link {
      const link = graph.edge(peer, this.id)
      if (!link) {
        logger.fatal({source: peer, target: this.id}, "upstream link not found");
        throw new Error("upstream link not found");
      }
      return graph.getEdgeAttributes(link)
  }

}
