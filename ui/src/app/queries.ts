import {
  EMessageType,
  ILink,
  INode,
  IServerMessage,
} from "@/components/Graph/types";
import { parse } from "@iarna/toml";
import { closeSync, createReadStream, openSync, readSync, statSync } from "fs";
import path from "path";
import { messagesPath } from "./api/utils";

export const getSetSimulationMaxTime = async (): Promise<number> => {
  return new Promise((resolve, reject) => {
    const fileSize = statSync(messagesPath).size;
    const bufferSize = 1024;
    if (fileSize === 0) {
      return reject(new Error("File is empty"));
    }

    const fileDescriptor = openSync(messagesPath, "r");
    let buffer = Buffer.alloc(bufferSize);
    let position = fileSize;
    let lastLine = "";
    let foundLastTransactionReceived = false;

    while (position > 0 && !foundLastTransactionReceived) {
      // Calculate how many bytes to read
      const bytesToRead = Math.min(bufferSize, position);
      position -= bytesToRead;

      // Read from the file
      readSync(
        fileDescriptor,
        new Uint8Array(buffer.buffer),
        0,
        bytesToRead,
        position,
      );
      const chunk = buffer.toString("utf8", 0, bytesToRead);

      // Search for the last newline character
      const lines = chunk.split(/\n/).reverse();
      for (const line of lines) {
        if (!line) {
          continue;
        }

        try {
          const message: IServerMessage = JSON.parse(line);
          if (message.message.type === EMessageType.TransactionReceived) {
            lastLine = line;
            foundLastTransactionReceived = true;
            break;
          }
        } catch (e) {
          console.log(`Could not parse: ${line}`);
        }
      }

      position -= bytesToRead;
    }

    closeSync(fileDescriptor);

    if (!foundLastTransactionReceived && lastLine.length === 0) {
      return reject(new Error("Could not find any complete line in the file"));
    }

    if (!lastLine) {
      reject("Could not find the last transaction.");
    } else {
      const message: IServerMessage = JSON.parse(lastLine.trim());
      resolve(message.time / 1_000_000);
    }
  });
};

export const getSimulationTopography = async () => {
  const filePath = path.resolve(
    __dirname,
    "../../../../../sim-rs/test_data/medium.toml",
  );
  const fileStream = createReadStream(filePath, {
    encoding: "utf8",
    highWaterMark: 100_000,
  });
  const result = (await parse.stream(fileStream)) as unknown as {
    links: ILink[];
    nodes: INode[];
  };

  const sanitizeBigints = (_: string, v: any) =>
    typeof v === "bigint" ? `${v}n` : v;
  const restoreBigints = (_: string, v: any) =>
    typeof v === "string" && /^\d+n$/.test(v) ? BigInt(v.replace("n", "")) : v;

  // Must sanitize the objects to exclude symbols from the TOML parser.
  const sanitized = JSON.parse(
    JSON.stringify(
      {
        links: result.links,
        nodes: result.nodes,
      },
      sanitizeBigints,
    ),
    restoreBigints,
  );

  return sanitized;
};
