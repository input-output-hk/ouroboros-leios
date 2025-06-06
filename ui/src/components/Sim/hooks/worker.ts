import { ISimulationAggregatedDataState, ISimulationBlock, ISimulationIntermediateDataState, ISimulationTransactionData } from '@/contexts/SimContext/types';
import * as cbor from 'cborg';
import type { ReadableStream } from 'stream/web';
import { IServerMessage } from '../types';
import { processMessage } from './utils';

export type TWorkerRequest =
  { type: "START", tracePath: string, aggregated: true, speedMultiplier: number } |
  { type: "START", tracePath: string, aggregated?: false, batchSize: number } |
  { type: "STOP" };

export type TWorkerResponse =
  { type: "EVENT", tracePath: string, aggregatedData: ISimulationAggregatedDataState } |
  { type: "DONE", tracePath: string };

const createEventStream = async <T>(path: string, signal: AbortSignal): Promise<ReadableStream<T>> => {
  const res = await fetch(path, { signal });
  if (!res.body) {
    throw new Error("body not streamed");
  }
  let stream = res.body;
  if (path.endsWith('.gz')) {
    path = path.substring(0, path.length - 3);
    if (res.headers.get('Content-Encoding') !== 'gzip') {
      stream = stream.pipeThrough(new DecompressionStream('gzip'));
    }
  }
  const transform = path.endsWith('.cbor') ? createCborTransformer() : createJsonTransformer();
  return stream.pipeThrough(transform) as unknown as ReadableStream<T>;
}

const createJsonTransformer = <T>(): TransformStream<Uint8Array, T> => {
  let buffer = "";
  const decoder = new TextDecoder();
  return new TransformStream({
    transform(chunk, controller) {
      buffer += decoder.decode(chunk);
      for (let nl = buffer.indexOf('\n'); nl != -1; nl = buffer.indexOf('\n')) {
        if (nl) {
          const message = JSON.parse(buffer.substring(0, nl));
          controller.enqueue(message);
        }
        buffer = buffer.substring(nl + 1);
      }
    }
  });
}

const createCborTransformer = <T>(): TransformStream<Uint8Array, T> => {
  let buffer: Buffer | null = null;
  return new TransformStream({
    transform(chunk, controller) {
      buffer = buffer ? Buffer.concat([buffer, chunk]) : Buffer.from(chunk);
      while (buffer != null) {
        try {
          const [value, unused] = cbor.decodeFirst(buffer);
          buffer = unused as Buffer;
          controller.enqueue(value);
        } catch (error: any) {
          if (error.message.startsWith('CBOR decode error:')) {
            break;
          } else {
            throw error;
          }
        }
      }
    }
  })
}

const consumeStream = async (
  stream: ReadableStream<IServerMessage>,
  tracePath: string,
  batchSize: number,
) => {
  const aggregatedData: ISimulationAggregatedDataState = {
    progress: 0,
    nodes: new Map(),
    global: {
      praosTxOnChain: 0,
      leiosTxOnChain: 0,
    },
    blocks: [],
    transactions: [],
    lastNodesUpdated: [],
  };
  const intermediate: ISimulationIntermediateDataState = {
    txs: [],
    txStatuses: [],
    leiosTxs: new Set(),
    praosTxs: new Set(),
    ibs: new Map(),
    ebs: new Map(),
    bytes: new Map(),
  };

  const nodesUpdated = new Set<string>();
  let batchEvents = 0;
  let lastSec = null;
  for await (const { time_s, message } of stream) {
    if (message.type.endsWith("Received") && "recipient" in message) {
      nodesUpdated.add(message.recipient);
    }
    if (message.type.endsWith("Sent") && "sender" in message) {
      nodesUpdated.add(message.sender);
    }
    if (message.type.endsWith("Generated") && "id" in message) {
      nodesUpdated.add(message.id);
    }
    processMessage({ time_s, message }, aggregatedData, intermediate);
    if (lastSec !== Math.floor(time_s)) {
      lastSec = Math.floor(time_s);
      aggregatedData.transactions.push(intermediate.txStatuses.reduce((acc, curr) => {
        acc[curr] += 1;
        return acc;
      }, {
        timestamp: lastSec,
        created: 0,
        inIb: 0,
        inEb: 0,
        onChain: 0,
      }));
    }
    aggregatedData.progress = time_s;
    batchEvents++;
    if (batchEvents === batchSize) {
      postMessage({
        type: "EVENT",
        tracePath,
        aggregatedData: {
          ...aggregatedData,
          lastNodesUpdated: [...nodesUpdated.values()],
        }
      } as TWorkerResponse);

      nodesUpdated.clear();
      batchEvents = 0;
    }
  }
  if (batchEvents) {
    postMessage({
      type: "EVENT",
      tracePath,
      aggregatedData: {
        ...aggregatedData,
        lastNodesUpdated: [...nodesUpdated.values()],
      }
    } as TWorkerResponse);
  }
  postMessage({ type: "DONE", tracePath });
}

const consumeAggregateStream = async (
  stream: ReadableStream<ISimulationAggregatedDataState>,
  tracePath: string,
  speedMultiplier: number,
) => {
  let lastTimestamp = 0;
  let blocks: ISimulationBlock[] = [];
  let transactions: ISimulationTransactionData[] = [];
  for await (const aggregatedData of stream) {
    const nodes = new Map();
    for (const [id, stats] of Object.entries(aggregatedData.nodes)) {
      nodes.set(id, stats);
    }
    aggregatedData.nodes = nodes;
    blocks.push(...aggregatedData.blocks);
    aggregatedData.blocks = blocks;
    transactions.push(...aggregatedData.transactions);
    aggregatedData.transactions = transactions;

    const elapsedMs = (aggregatedData.progress - lastTimestamp) * 1000;
    lastTimestamp = aggregatedData.progress;
    await new Promise(resolve => setTimeout(resolve, elapsedMs / speedMultiplier));

    postMessage({
      type: "EVENT",
      tracePath,
      aggregatedData,
    } as TWorkerResponse);
  }
  postMessage({ type: "DONE", tracePath });
}

let controller = new AbortController();
onmessage = (e: MessageEvent<TWorkerRequest>) => {
  controller.abort();
  const request = e.data;
  if (request.type === "STOP" || !request.tracePath) {
    return;
  }

  controller = new AbortController();
  if (request.aggregated) {
    createEventStream<ISimulationAggregatedDataState>(request.tracePath, controller.signal)
      .then(stream => consumeAggregateStream(stream, request.tracePath, request.speedMultiplier))
      .catch(err => {
        if (err.name !== "AbortError") {
          throw err;
        }
      });

  } else {
    createEventStream<IServerMessage>(request.tracePath, controller.signal)
      .then(stream => consumeStream(stream, request.tracePath, request.batchSize))
      .catch(err => {
        if (err.name !== "AbortError") {
          throw err;
        }
      });
  }
}