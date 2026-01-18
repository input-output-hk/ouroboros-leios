import TinyQueue from 'tinyqueue';
import { DirectedGraph } from 'graphology';
import type { TxId, Tx, Block } from './types.js';
import { Node } from './node.js';
import { Link } from './link.js';
import { logger } from './logger.js';

/**
 * Event types for the discrete event simulation.
 */
export type Event =
  | { kind: 'SubmitTx'; clock: number; to: string; tx: Tx }
  | { kind: 'OfferTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'RequestTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'SendTx'; clock: number; from: string; to: string; tx: Tx }
  | { kind: 'ProduceBlock'; clock: number; producer: string; blockSize_B: number };

/**
 * Simulation class that encapsulates the network graph and event queue.
 * This allows running multiple independent simulations and provides
 * better testability than global state.
 */
export class Simulation {
  private eventQueue: TinyQueue<Event>;
  private _graph: DirectedGraph<Node, Link>;
  private _currentTime: number = 0;
  private _eventsProcessed: number = 0;
  private _blocks: Block[] = [];

  constructor(graph: DirectedGraph<Node, Link>) {
    this._graph = graph;
    this.eventQueue = new TinyQueue<Event>([], (a, b) => a.clock - b.clock);
  }

  get graph(): DirectedGraph<Node, Link> {
    return this._graph;
  }

  get currentTime(): number {
    return this._currentTime;
  }

  get eventsProcessed(): number {
    return this._eventsProcessed;
  }

  get pendingEvents(): number {
    return this.eventQueue.length;
  }

  get blocks(): Block[] {
    return this._blocks;
  }

  /**
   * Submit a transaction to a node at a given time.
   */
  submitTx(clock: number, to: string, tx: Tx): void {
    this.eventQueue.push({
      kind: 'SubmitTx',
      clock,
      to,
      tx
    });
  }

  /**
   * Offer a transaction ID from one node to another.
   */
  offerTx(clock: number, from: string, to: string, txId: TxId): void {
    this.eventQueue.push({
      kind: 'OfferTx',
      clock,
      from,
      to,
      txId
    });
  }

  /**
   * Request a transaction from a peer.
   */
  requestTx(clock: number, from: string, to: string, txId: TxId): void {
    this.eventQueue.push({
      kind: 'RequestTx',
      clock,
      from,
      to,
      txId
    });
  }

  /**
   * Send a transaction to a peer.
   */
  sendTx(clock: number, from: string, to: string, tx: Tx): void {
    this.eventQueue.push({
      kind: 'SendTx',
      clock,
      from,
      to,
      tx
    });
  }

  /**
   * Schedule block production at a given time.
   */
  produceBlock(clock: number, producer: string, blockSize_B: number): void {
    this.eventQueue.push({
      kind: 'ProduceBlock',
      clock,
      producer,
      blockSize_B
    });
  }

  /**
   * Record a produced block.
   */
  recordBlock(block: Block): void {
    this._blocks.push(block);
    logger.info({
      blockId: block.blockId,
      producer: block.producer,
      timestamp: block.timestamp,
      txCount: block.transactions.length,
      size_B: block.size_B,
      honestCount: block.honestCount,
      adversarialCount: block.adversarialCount
    }, "block produced");
  }

  /**
   * Process all events in the queue until empty.
   */
  run(): void {
    while (this.eventQueue.length > 0) {
      this.step();
    }
  }

  /**
   * Process a single event from the queue.
   * Returns true if an event was processed, false if queue is empty.
   */
  step(): boolean {
    const event = this.eventQueue.pop();
    if (!event) {
      return false;
    }

    this._currentTime = event.clock;
    this._eventsProcessed++;

    // Handle ProduceBlock separately since it has 'producer' not 'to'
    if (event.kind === 'ProduceBlock') {
      const producer: Node = this._graph.getNodeAttributes(event.producer);
      if (!producer) {
        logger.fatal(event, "unknown producer node");
        throw new Error(`unknown producer node: ${event.producer}`);
      }
      producer.handleProduceBlock(this, event.clock, event.blockSize_B);
      return true;
    }

    const target: Node = this._graph.getNodeAttributes(event.to);
    if (!target) {
      logger.fatal(event, "unknown target node");
      throw new Error(`unknown target node: ${event.to}`);
    }

    switch (event.kind) {
      case 'SubmitTx':
        target.handleSubmitTx(this, event.clock, event.tx);
        break;
      case 'OfferTx':
        target.handleOfferTx(this, event.clock, event.from, event.txId);
        break;
      case 'RequestTx':
        target.handleRequestTx(this, event.clock, event.from, event.txId);
        break;
      case 'SendTx':
        target.handleSendTx(this, event.clock, event.from, event.tx);
        break;
    }

    return true;
  }

  /**
   * Reset the simulation state (clears event queue, resets counters).
   * Note: Does not reset node states - create a new Simulation for that.
   */
  reset(): void {
    this.eventQueue = new TinyQueue<Event>([], (a, b) => a.clock - b.clock);
    this._currentTime = 0;
    this._eventsProcessed = 0;
    this._blocks = [];
  }
}
