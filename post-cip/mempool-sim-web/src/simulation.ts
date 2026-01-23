import TinyQueue from 'tinyqueue';
import { DirectedGraph } from 'graphology';
import type { TxId, Tx, Block, P2PConfig } from './types.js';
import { Node } from './node.js';
import { Link } from './link.js';
import { logger } from './logger.js';
import type { ChurnResult } from './peer-manager.js';

/**
 * Event types for the discrete event simulation.
 */
export type Event =
  | { kind: 'SubmitTx'; clock: number; to: string; tx: Tx }
  | { kind: 'OfferTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'RequestTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'SendTx'; clock: number; from: string; to: string; tx: Tx }
  | { kind: 'ProduceBlock'; clock: number; producer: string; blockSize_B: number }
  | { kind: 'PeerChurn'; clock: number; nodeId: string };

/**
 * Extended PeerChurn event with churn result for visualization.
 */
export type PeerChurnEvent = { kind: 'PeerChurn'; clock: number; nodeId: string; churnResult: ChurnResult | null };

/**
 * Event type passed to handler, which includes churnResult for PeerChurn events.
 */
export type HandlerEvent =
  | Exclude<Event, { kind: 'PeerChurn' }>
  | PeerChurnEvent;

/**
 * Event handler callback for visualization or logging purposes.
 */
export type SimulationEventHandler = (event: HandlerEvent) => void;

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
  private _eventHandler: SimulationEventHandler | null = null;
  private _p2pConfig: P2PConfig | null = null;
  private _p2pEndTime: number = Infinity;

  constructor(graph: DirectedGraph<Node, Link>) {
    this._graph = graph;
    this.eventQueue = new TinyQueue<Event>([], (a, b) => a.clock - b.clock);
  }

  /**
   * Set an optional event handler for visualization or logging.
   */
  setEventHandler(handler: SimulationEventHandler | null): void {
    this._eventHandler = handler;
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

  get p2pConfig(): P2PConfig | null {
    return this._p2pConfig;
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
   * Schedule a peer churn event for a node.
   * Only schedules if the clock time is before the P2P end time.
   */
  schedulePeerChurn(clock: number, nodeId: string): void {
    if (clock > this._p2pEndTime) {
      return;
    }
    this.eventQueue.push({
      kind: 'PeerChurn',
      clock,
      nodeId
    });
  }

  /**
   * Initialize P2P peer selection for all nodes.
   * Sets up peer managers and schedules initial churn events.
   * @param config P2P configuration
   * @param endTime Maximum simulation time (churn events won't be scheduled beyond this)
   */
  initializeP2P(config: P2PConfig, endTime: number = Infinity): void {
    if (!config.enabled) {
      return;
    }

    this._p2pConfig = config;
    this._p2pEndTime = endTime;

    // Collect all node IDs for peer selection pool
    const allNodeIds: string[] = [];
    this._graph.forEachNode((nodeId) => {
      allNodeIds.push(nodeId);
    });

    // Initialize each node's peer manager with topology info
    this._graph.forEachNode((nodeId) => {
      const node = this._graph.getNodeAttributes(nodeId);

      // Upstream peers are nodes that have edges TO this node (in-edges)
      const upstreamPeers: string[] = [];
      this._graph.forEachInEdge(nodeId, (_edge, _attr, source) => {
        upstreamPeers.push(source);
      });

      node.initializeP2P(config.churnProbability, upstreamPeers, allNodeIds);

      // Schedule initial churn event
      this.schedulePeerChurn(config.churnInterval, nodeId);
    });

    logger.info({
      churnInterval: config.churnInterval,
      churnProbability: config.churnProbability,
    }, 'P2P peer selection initialized');
  }

  /**
   * Diffuse a produced block and remove confirmed transactions from all nodes.
   * Since honest and adversarial txs share UTxO inputs, when either is confirmed
   * the other becomes invalid and should be removed from all mempools.
   */
  diffuseBlock(block: Block): void {
    this._blocks.push(block);
    logger.info({
      blockId: block.blockId,
      producer: block.producer,
      clock: block.clock,
      txCount: block.transactions.length,
      size_B: block.size_B,
      honestCount: block.honestCount,
      adversarialCount: block.adversarialCount
    }, "block produced");
    logger.debug(block, "block contents");

    // Build list of all txIds to remove (both honest and adversarial variants)
    const txIdsToRemove: string[] = [];
    for (const tx of block.transactions) {
      if (tx.frontRuns === '') {
        // Honest tx: remove it and its adversarial variant
        txIdsToRemove.push(tx.txId);
        txIdsToRemove.push(tx.txId + 'adv');
      } else {
        // Adversarial tx: remove it and the original honest tx it front-runs
        txIdsToRemove.push(tx.txId);
        txIdsToRemove.push(tx.frontRuns);
      }
    }

    // Remove from all nodes' mempools
    this._graph.forEachNode((nodeId) => {
      const node = this._graph.getNodeAttributes(nodeId);
      node.removeConfirmedTxs(this, block.clock, txIdsToRemove);
    });
    
    this.eventQueue.data =
      this.eventQueue.data.filter(e => {
        switch (e.kind) {
          case 'SubmitTx': return !txIdsToRemove.includes(e.tx.txId);
          case 'OfferTx': return !txIdsToRemove.includes(e.txId);
          case 'RequestTx': return !txIdsToRemove.includes(e.txId);
          case 'SendTx': return !txIdsToRemove.includes(e.tx.txId);
          case 'ProduceBlock': return true;
          case 'PeerChurn': return true;
        }
      });
    this.eventQueue.length = this.eventQueue.data.length;
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

    // Notify event handler if set (except PeerChurn which is handled separately with churnResult)
    if (this._eventHandler && event.kind !== 'PeerChurn') {
      this._eventHandler(event);
    }

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

    // Handle PeerChurn separately since it has 'nodeId' not 'to'
    if (event.kind === 'PeerChurn') {
      const node: Node = this._graph.getNodeAttributes(event.nodeId);
      if (!node) {
        logger.fatal(event, "unknown node for churn");
        throw new Error(`unknown node for churn: ${event.nodeId}`);
      }
      const churnResult = node.handlePeerChurn(this, event.clock);
      // Notify handler with extended event including churnResult
      if (this._eventHandler) {
        this._eventHandler({ ...event, churnResult });
      }
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
    this._p2pConfig = null;
  }

  /**
   * Peek at the next event time without processing it.
   */
  peekNextEventTime(): number | null {
    const event = this.eventQueue.peek();
    return event ? event.clock : null;
  }
}
