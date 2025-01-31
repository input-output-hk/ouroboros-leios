import {
  EMessageType,
  ILink,
  INode,
  IServerMessage,
  IServerNodeMap
} from "@/components/Sim/types";
import { closeSync, openSync, readFile, readSync, statSync } from "fs";
import path from "path";
import { promisify } from "util";
import { parse } from "yaml";
import { Coord2D, Node as IServerNode } from '../../../data/simulation/topology';
import { messagesPath } from "./api/utils";

const readFileAsync = promisify(readFile);

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

export const getSimulationTopography = async (): Promise<IServerNodeMap> => {
  const filePath = path.resolve(
    __dirname,
    "../../../../../sim-rs/test_data/thousand.yaml",
  );
  const file = await readFileAsync(filePath, { encoding: 'utf8' });
  const yaml = parse(file);

  const nodes: INode[] = [];
  const links = new Map<String, ILink>();
  for (const [id, node] of Object.entries<IServerNode<Coord2D>>(yaml.nodes)) {
    nodes.push({
      id,
      location: node.location,
      stake: node.stake as unknown as number,
    });
    for (const peerId of Object.keys(node.producers)) {
      const linkIds = [id, peerId].sort();
      links.set(JSON.stringify(linkIds), { nodes: linkIds });
    }
  }

  return { nodes, links: [...links.values()] };
}
