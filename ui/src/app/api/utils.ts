import { IServerMessage } from "@/components/Sim/types";
import * as cbor from 'cbor';
import * as fs from 'fs/promises';
import path from "path";
import { ReadableStream, ReadableStreamDefaultReader } from "stream/web";

export const messagesPath = path.resolve(
  __dirname,
  "../../../../../../sim-rs/output/messages.jsonl",
);

export type EventStream = ReadableStream<IServerMessage>;
export type EventStreamReader = ReadableStreamDefaultReader<IServerMessage>;

export const createEventStream = (path: string) => {
  if (path.endsWith('.cbor')) {
    return createCborEventStream(path);
  }
  return createJsonEventStream(path);
};

const createJsonEventStream = (path: string): EventStream => {
  let handle: fs.FileHandle;
  let buffer = "";
  return new ReadableStream({
    async start() {
      handle = await fs.open(path, 'r');
    },
    async pull(controller) {
      let readSomething = false;
      while (!readSomething) {
        const { bytesRead, buffer: chunk } = await handle.read();
        if (bytesRead === 0) {
          handle.close();
          controller.close();
          return;
        } else {
          buffer += chunk.toString('utf8', 0, bytesRead);
          for (let nl = buffer.indexOf('\n'); nl != -1; nl = buffer.indexOf('\n')) {
            if (nl) {
              const message = JSON.parse(buffer.substring(0, nl));
              controller.enqueue(message);
              readSomething = true;
            }
            buffer = buffer.substring(nl + 1);
          }
        }
      }
    },
    async cancel() {
      await handle.close();
    }
  });
}

const createCborEventStream = (path: string): EventStream => {
  let handle: fs.FileHandle;
  let buffer: Buffer | null = null;

  return new ReadableStream({
    async start() {
      handle = await fs.open(path, 'r');
    },
    async pull(controller) {
      let readSomething = false;
      while (!readSomething) {
        const { bytesRead, buffer: chunk } = await handle.read();
        if (bytesRead === 0) {
          handle.close();
          controller.close();
          return;
        } else {
          buffer = buffer ? Buffer.concat([buffer, chunk], buffer.length + bytesRead) : chunk;
          while (buffer != null) {
            try {
              const { value, unused } = cbor.decodeFirstSync(buffer, { extendedResults: true });
              buffer = unused as Buffer;
              controller.enqueue(value);
              readSomething = true;
            } catch (error: any) {
              if (error.message === 'Insufficient data') {
                break;
              } else {
                throw error;
              }
            }
          }
        }
      }
    },
    async cancel() {
      await handle.close();
    }
  });

}
