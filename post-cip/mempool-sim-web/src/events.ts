import TinyQueue from 'tinyqueue';
import { DirectedGraph } from 'graphology';
import type { TxId, Tx } from './types.js';
import { Node } from './node.js';
import { Link } from './link.js';
import { logger } from './logger.js';


export type Event = 
  | { kind: 'SubmitTx'; clock: number; to: string; tx: Tx }
  | { kind: 'OfferTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'RequestTx'; clock: number; from: string; to: string; txId: TxId }
  | { kind: 'SendTx'; clock: number; from: string; to: string; tx: Tx }
  | { kind: 'ReceiveTx'; clock: number; from: string; to: string; tx: Tx };


const EventQueue = new TinyQueue<Event>([], (a, b) => a.clock - b.clock);


export const submitTx = (clock: number, to: string, tx: Tx): void =>
  EventQueue.push({
    kind: 'SubmitTx',
    clock,
    to,
    tx
  });

export const offerTx = (clock: number, from: string, to: string, txId: TxId): void => 
  EventQueue.push({
    kind: 'OfferTx',
    clock,
    from,
    to,
    txId
  });

export const requestTx = (clock: number, from: string, to: string, txId: TxId): void => 
  EventQueue.push({
    kind: 'RequestTx',
    clock,
    from,
    to,
    txId
  });

export const sendTx = (clock: number, from: string, to: string, tx: Tx): void => 
  EventQueue.push({
    kind: 'SendTx',
    clock,
    from,
    to,
    tx
  });

export const receiveTx = (clock: number, from: string, to: string, tx: Tx): void => 
  EventQueue.push({
    kind: 'ReceiveTx',
    clock,
    from,
    to,
    tx
  });

export const handleEvents = (graph: DirectedGraph<Node, Link>): void => {
  while (EventQueue.length > 0) {
    const event = EventQueue.pop();
    if (!event)
      break;
    logger.info(event, "Handle event");
    const target: Node = graph.getNodeAttributes(event.to);
    if (!target)
      throw new Error("Unknown node: ${event.to}");
    switch (event.kind) {
      case 'SubmitTx':
        target.handleSubmitTx(graph, event.clock, event.tx);
        break;
      case 'OfferTx':
        target.handleOfferTx(graph, event.clock, event.from, event.txId);
        break;
      default:
        throw new Error("No handler for event.")
    }
  }
}
