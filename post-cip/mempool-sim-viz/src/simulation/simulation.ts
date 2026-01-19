import TinyQueue from 'tinyqueue';
import { DirectedGraph } from 'graphology';
import type { TxId, Tx, Block } from './types';
import { Node } from './node';
import { Link } from './link';
import { logger } from './logger';

export type Event =
  | { kind: 'SubmitTx'; clock: number; to: string; tx: Tx }
  | { kind: 'OfferTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'RequestTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'SendTx'; clock: number; from: string; to: string; tx: Tx }
  | { kind: 'ProduceBlock'; clock: number; producer: string; blockSize_B: number };

export type SimulationEventHandler = (event: Event) => void;

export class Simulation {
  private eventQueue: TinyQueue<Event>;
  private _graph: DirectedGraph<Node, Link>;
  private _currentTime: number = 0;
  private _eventsProcessed: number = 0;
  private _blocks: Block[] = [];
  private _eventHandler: SimulationEventHandler | null = null;

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

  setEventHandler(handler: SimulationEventHandler | null): void {
    this._eventHandler = handler;
  }

  submitTx(clock: number, to: string, tx: Tx): void {
    this.eventQueue.push({
      kind: 'SubmitTx',
      clock,
      to,
      tx
    });
  }

  offerTx(clock: number, from: string, to: string, txId: TxId): void {
    this.eventQueue.push({
      kind: 'OfferTx',
      clock,
      from,
      to,
      txId
    });
  }

  requestTx(clock: number, from: string, to: string, txId: TxId): void {
    this.eventQueue.push({
      kind: 'RequestTx',
      clock,
      from,
      to,
      txId
    });
  }

  sendTx(clock: number, from: string, to: string, tx: Tx): void {
    this.eventQueue.push({
      kind: 'SendTx',
      clock,
      from,
      to,
      tx
    });
  }

  produceBlock(clock: number, producer: string, blockSize_B: number): void {
    this.eventQueue.push({
      kind: 'ProduceBlock',
      clock,
      producer,
      blockSize_B
    });
  }

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

    // Propagate confirmed txs to all nodes (simulates block propagation)
    // This removes the txs from all nodes' mempools
    // Also removes conflicting txs (UTXO semantics):
    // - If honest tx included, remove its adversarial version (txId + "adv")
    // - If adversarial tx included, remove the honest tx it front-runs
    const txIdsToRemove: string[] = [];
    for (const tx of block.transactions) {
      txIdsToRemove.push(tx.txId);
      if (tx.frontRuns === '') {
        // Honest tx included - invalidate adversarial version
        txIdsToRemove.push(tx.txId + 'adv');
      } else {
        // Adversarial tx included - invalidate honest version
        txIdsToRemove.push(tx.frontRuns);
      }
    }

    this._graph.forEachNode((nodeId) => {
      if (nodeId !== block.producer) {
        const node = this._graph.getNodeAttributes(nodeId);
        node.removeConfirmedTxs(txIdsToRemove);
      }
    });
  }

  run(): void {
    while (this.eventQueue.length > 0) {
      this.step();
    }
  }

  step(): boolean {
    const event = this.eventQueue.pop();
    if (!event) {
      return false;
    }

    this._currentTime = event.clock;
    this._eventsProcessed++;

    if (this._eventHandler) {
      this._eventHandler(event);
    }

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

  peekNextEventTime(): number | null {
    const event = this.eventQueue.peek();
    return event ? event.clock : null;
  }

  reset(): void {
    this.eventQueue = new TinyQueue<Event>([], (a, b) => a.clock - b.clock);
    this._currentTime = 0;
    this._eventsProcessed = 0;
    this._blocks = [];
  }
}
