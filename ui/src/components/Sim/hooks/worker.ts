import {
  ISimulationAggregatedDataState,
} from "@/contexts/SimContext/types";
import * as cbor from "cborg";
import type { ReadableStream } from "stream/web";
import { IServerMessage, EServerMessageType } from "../types";

export type TWorkerRequest =
  | {
      type: "START";
      tracePath: string;
      aggregated: true;
      speedMultiplier: number;
    }
  | {
      type: "START";
      tracePath: string;
      aggregated?: false;
      includeTransactions?: boolean;
    }
  | { type: "STOP" };

export type TWorkerResponse =
  | {
      type: "TIMELINE_EVENTS";
      tracePath: string;
      events: IServerMessage[];
    }
  | { type: "DONE"; tracePath: string };

const createEventStream = async <T>(
  path: string,
  signal: AbortSignal,
): Promise<ReadableStream<T>> => {
  const res = await fetch(path, { signal });
  if (!res.body) {
    throw new Error("body not streamed");
  }
  let stream = res.body;
  if (path.endsWith(".gz")) {
    path = path.substring(0, path.length - 3);
    if (res.headers.get("Content-Encoding") !== "gzip") {
      stream = stream.pipeThrough(new DecompressionStream("gzip"));
    }
  }
  const transform = path.endsWith(".cbor")
    ? createCborTransformer()
    : createJsonTransformer();
  return stream.pipeThrough(transform) as unknown as ReadableStream<T>;
};

const createJsonTransformer = <T>(): TransformStream<Uint8Array, T> => {
  let buffer = "";
  const decoder = new TextDecoder();
  return new TransformStream({
    transform(chunk, controller) {
      buffer += decoder.decode(chunk);
      for (let nl = buffer.indexOf("\n"); nl != -1; nl = buffer.indexOf("\n")) {
        if (nl) {
          const message = JSON.parse(buffer.substring(0, nl));
          controller.enqueue(message);
        }
        buffer = buffer.substring(nl + 1);
      }
    },
  });
};

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
          if (error.message.startsWith("CBOR decode error:")) {
            break;
          } else {
            throw error;
          }
        }
      }
    },
  });
};

// Base event types (always included)
const BASE_VISUALIZATION_EVENTS = new Set([
  EServerMessageType.EBGenerated,
  EServerMessageType.EBSent,
  EServerMessageType.EBReceived,
  EServerMessageType.RBGenerated,
  EServerMessageType.RBSent,
  EServerMessageType.RBReceived,
  EServerMessageType.VTBundleGenerated,
  EServerMessageType.VTBundleSent,
  EServerMessageType.VTBundleReceived,
]);

// Transaction events (optional)
const TRANSACTION_EVENTS = new Set([
  EServerMessageType.TransactionGenerated,
  EServerMessageType.TransactionSent,
  EServerMessageType.TransactionReceived,
]);

const consumeStream = async (
  stream: ReadableStream<IServerMessage>,
  tracePath: string,
  includeTransactions = false,
) => {
  // Build event filter based on settings
  const allowedEvents = new Set(BASE_VISUALIZATION_EVENTS);
  if (includeTransactions) {
    TRANSACTION_EVENTS.forEach((event) => allowedEvents.add(event));
  }

  let eventCount = 0;
  let filteredCount = 0;
  let batchCount = 0;
  const startTime = performance.now();
  let batchStart = performance.now();

  // Batch events to reduce postMessage overhead
  const batch: IServerMessage[] = [];
  const BATCH_SIZE = includeTransactions ? 10000 : 1000; // Larger batches for high-volume scenarios

  const flushBatch = () => {
    if (batch.length > 0) {
      postMessage({
        type: "TIMELINE_EVENTS",
        tracePath,
        events: batch.splice(0),
      } as TWorkerResponse);
      batchCount++;
    }
  };

  for await (const serverMessage of stream) {
    eventCount++;
    const { message } = serverMessage;

    // Filter only visualization-relevant events
    if (message.type !== "__unknown" && allowedEvents.has(message.type)) {
      filteredCount++;
      batch.push(serverMessage);

      if (batch.length >= BATCH_SIZE) {
        flushBatch();
        // Log progress every batch
        const batchEnd = performance.now();
        console.log(
          `Worker progress: ${eventCount} events, ${filteredCount} filtered, ${batchCount} messages sent, batch ${(batchEnd - batchStart).toFixed(2)}ms`,
        );
        batchStart = performance.now();
      }
    }
  }

  // Flush remaining batch
  flushBatch();

  const totalTime = performance.now() - startTime;
  console.log(
    `Worker completed: ${eventCount} events processed, ${filteredCount} filtered, ${batchCount} batches sent in ${totalTime.toFixed(0)}ms`,
  );

  postMessage({ type: "DONE", tracePath });
};

// TODO: unused
const consumeAggregateStream = async (
  stream: ReadableStream<ISimulationAggregatedDataState>,
  tracePath: string,
  speedMultiplier: number,
) => {
  let lastTimestamp = 0;
  for await (const aggregatedData of stream) {
    const nodes = new Map();
    for (const [id, stats] of Object.entries(aggregatedData.nodes)) {
      nodes.set(id, stats);
    }
    aggregatedData.nodes = nodes;

    const elapsedMs = (aggregatedData.progress - lastTimestamp) * 1000;
    lastTimestamp = aggregatedData.progress;
    await new Promise((resolve) =>
      setTimeout(resolve, elapsedMs / speedMultiplier),
    );

    // TODO: re-create when needed
    // postMessage({
    //   type: "EVENT",
    //   tracePath,
    //   aggregatedData,
    // } as TWorkerResponse);
  }
  postMessage({ type: "DONE", tracePath });
};

let controller = new AbortController();
onmessage = (e: MessageEvent<TWorkerRequest>) => {
  controller.abort();
  const request = e.data;
  if (request.type === "STOP" || !request.tracePath) {
    return;
  }

  controller = new AbortController();
  if (request.aggregated) {
    createEventStream<ISimulationAggregatedDataState>(
      request.tracePath,
      controller.signal,
    )
      .then((stream) =>
        consumeAggregateStream(
          stream,
          request.tracePath,
          request.speedMultiplier,
        ),
      )
      .catch((err) => {
        if (err.name !== "AbortError") {
          throw err;
        }
      });
  } else {
    createEventStream<IServerMessage>(request.tracePath, controller.signal)
      .then((stream) =>
        consumeStream(stream, request.tracePath, request.includeTransactions),
      )
      .catch((err) => {
        if (err.name !== "AbortError") {
          throw err;
        }
      });
  }
};
