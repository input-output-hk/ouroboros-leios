import { IServerMessage } from "@/components/Sim/types";
import * as cbor from 'cbor';
import { createReadStream, ReadStream } from "fs";
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

export const getMaxTime = (path: string) => {
  if (path.endsWith('.cbor')) {
    return getCborMaxTime(path);
  }
  return getJsonMaxTime(path);
}

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

const getJsonMaxTime = async (path: string): Promise<number> => {
  const chunkSize = 1024;
  const handle = await fs.open(path, "r");
  const { size } = await handle.stat();
  let filepos = size - chunkSize;
  let text = "";
  let index = 0;
  while (filepos >= 0) {
    let { buffer, bytesRead } = await handle.read({ position: filepos, length: chunkSize });
    text = buffer.toString('utf-8', 0, bytesRead) + text;
    index += bytesRead;
    let nl = text.lastIndexOf('\n', index);
    while (nl >= 0) {
      const raw = text.substring(nl + 1, index);
      try {
        const event: IServerMessage = JSON.parse(raw);
        await handle.close();
        return event.time;
      } catch (err) { }
      index = nl;
      nl = index == 0 ? -1 : text.lastIndexOf('\n', index - 1);
    }
    filepos -= chunkSize;
  }
  await handle.close();
  throw new Error("Last line not found");
}

/*
const createCborEventStream = (path: string): EventStream => {
  let handle: fs.FileHandle;
  let buffer: Buffer | null = null;

  const decoder = new cbor.Decoder();
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
          try {
            decoder.decodeMultiple(buffer, event => {
              console.log({ event });
              controller.enqueue(event);
              readSomething = true;
            }) as any;
            buffer = null;
          } catch (err: any) {
            if (err.incomplete) {
              buffer = buffer!.subarray(err.lastPosition);
            } else {
              throw err;
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
*/

const createCborEventStreamm = (path: string): EventStream => {
  let buffer: ReadStream;
  return new ReadableStream({
    async start() {
      buffer = createReadStream(path);
    },
    async pull(controller) {
      try {
        const event = await cbor.decodeFirst(buffer, { extendedResults: true });
        console.log({ event });
        controller.enqueue(event.value);
      } catch (err) {
        controller.close();
        console.log({ err });
      }
    },
    async cancel() {
      buffer.close();
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

const getCborMaxTime = async (path: string): Promise<number> => {
  const stream = createCborEventStream(path);
  let lastEvent: IServerMessage | null = null;
  for await (const event of stream) {
    lastEvent = event;
  }
  if (!lastEvent) {
    throw new Error('No events found');
  }
  return lastEvent.time;
}