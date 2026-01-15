import TinyQueue from 'tinyqueue';
import { DirectedGraph } from 'graphology';
import type { TxId, Tx } from './types.js';
import { Node } from './node.js';
import { Link } from './link.js';
import { logger } from './logger.js';


export type Event = 
  | { kind: 'SubmitTx'; timestamp: number; to: string; tx: Tx }
  | { kind: 'OfferTx'; timestamp: number; from: string; to: string; txId: TxId }
  | { kind: 'RequestTx'; timestamp: number; from: string; to: string; txId: TxId }
  | { kind: 'SendTx'; timestamp: number; from: string; to: string; tx: Tx }
  | { kind: 'ReceiveTx'; timestamp: number; from: string; to: string; tx: Tx };


const EventQueue = new TinyQueue<Event>([], (a, b) => a.timestamp - b.timestamp);


export const submitTx = (timestamp: number, to: string, tx: Tx): void =>
  EventQueue.push({
    kind: 'SubmitTx',
    timestamp,
    to,
    tx
  });

export const offerTx = (timestamp: number, from: string, to: string, txId: TxId): void => 
  EventQueue.push({
    kind: 'OfferTx',
    timestamp,
    from,
    to,
    txId
  });

export const requestTx = (timestamp: number, from: string, to: string, txId: TxId): void => 
  EventQueue.push({
    kind: 'RequestTx',
    timestamp,
    from,
    to,
    txId
  });

export const sendTx = (timestamp: number, from: string, to: string, tx: Tx): void => 
  EventQueue.push({
    kind: 'SendTx',
    timestamp,
    from,
    to,
    tx
  });

export const receiveTx = (timestamp: number, from: string, to: string, tx: Tx): void => 
  EventQueue.push({
    kind: 'ReceiveTx',
    timestamp,
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
        target.handleSubmitTx(graph, event.timestamp, event.tx);
        break;
      case 'OfferTx':
        target.handleOfferTx(graph, event.timestamp, event.from, event.txId);
        break;
      default:
        throw new Error("No handler for event.")
    }
  }
}
