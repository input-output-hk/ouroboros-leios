import { createReadStream } from "fs";
import { NextResponse } from "next/server";
import readline from "readline";

import { EMessageType, IServerMessage } from "@/components/Sim/types";
import { ISimulationAggregatedDataState, ISimulationIntermediateDataState } from "@/contexts/SimContext/types";
import { messagesPath } from "../../utils";
import { processMessage } from "./utils";

function getTimestampAtPosition(
  filePath: string,
  position: number,
): Promise<number> {
  return new Promise((resolve, reject) => {
    const stream = createReadStream(filePath, { start: position });
    let foundNewLine = false;
    let adjustedPosition = position;

    // Read a few bytes to find the newline character
    stream.on("data", (chunk) => {
      const decoded = chunk.toString("utf8");
      for (let i = 0; i < decoded.length; i++) {
        if (decoded[i] === "\n") {
          foundNewLine = true;
          adjustedPosition += i + 1; // Move to the start of the next line
          break;
        }
      }

      stream.close(); // Stop reading once the newline is found
    });

    stream.on("close", () => {
      if (foundNewLine) {
        // Now use readline to get the timestamp from the new line
        const lineStream = createReadStream(filePath, {
          start: adjustedPosition,
        });
        const rl = readline.createInterface({
          input: lineStream,
          crlfDelay: Infinity,
        });

        rl.on("line", (line) => {
          const message: IServerMessage = JSON.parse(line);
          const timestamp = message.time / 1_000_000;
          rl.close();
          resolve(timestamp);
        });

        rl.on("error", (err) => {
          reject(err);
        });
      } else {
        reject(
          new Error("Could not find a newline character in the provided range"),
        );
      }
    });

    stream.on("error", (err) => {
      reject(err);
    });
  });
}

export async function GET(req: Request, res: Response) {
  try {
    const url = new URL(req.url);
    const batchSize = url.searchParams.get("batchSize");

    if (isNaN(Number(batchSize))) {
      throw new Error("Invalid batch size.");
    }

    const fileStream = createReadStream(messagesPath, {
      encoding: "utf8",
    });
    const rl = readline.createInterface({
      input: fileStream,
      crlfDelay: Infinity,
    });

    let interval: Timer | undefined;
    const eventBuffer: string[] = [];
    let simulationDone = false;
    let isProcessing = false;

    const stream = new ReadableStream({
      cancel() {
        clearInterval(interval);
        rl.close();
        fileStream.close();
      },

      start(controller) {
        const aggregatedData: ISimulationAggregatedDataState = {
          progress: 0,
          nodes: new Map(),
          global: {
            praosTxOnChain: 0,
            leiosTxOnChain: 0,
          },
          blocks: [],
          lastNodesUpdated: [],
        };
        const intermediate: ISimulationIntermediateDataState = {
          txs: [],
          ibs: new Map(),
          ebs: new Map(),
        };

        interval = setInterval(() => {
          if (isProcessing) {
            return;
          }

          isProcessing = true;
          if (eventBuffer.length === 0 && simulationDone) {
            clearInterval(interval);
            rl.close();
            fileStream.close();
            controller.close();
            return;
          }

          try {
            // Process 10k events at a time.
            const batch = eventBuffer.splice(0, Number(batchSize));
            const nodesUpdated = new Set<string>();
            for (const line of batch) {
              const data: IServerMessage = JSON.parse(line);
              if (
                data.message.type === EMessageType.EndorserBlockGenerated ||
                data.message.type === EMessageType.InputBlockGenerated ||
                data.message.type === EMessageType.PraosBlockGenerated ||
                data.message.type === EMessageType.TransactionGenerated
              ) {
                nodesUpdated.add(data.message.id);
              } else if (
                data.message.type === EMessageType.EndorserBlockReceived ||
                data.message.type === EMessageType.InputBlockReceived ||
                data.message.type === EMessageType.PraosBlockReceived ||
                data.message.type === EMessageType.VotesReceived ||
                data.message.type === EMessageType.TransactionReceived
              ) {
                nodesUpdated.add(data.message.recipient.toString())
              } else if (
                data.message.type === EMessageType.EndorserBlockSent ||
                data.message.type === EMessageType.InputBlockSent ||
                data.message.type === EMessageType.PraosBlockSent ||
                data.message.type === EMessageType.VotesSent ||
                data.message.type === EMessageType.TransactionSent
              ) {
                nodesUpdated.add(data.message.sender.toString())
              }

              processMessage(data, aggregatedData, intermediate);
            }

            const serializedData = {
              ...aggregatedData,
              progress: JSON.parse(batch[batch.length - 1]).time / 1_000_000,
              nodes: Array.from(aggregatedData.nodes.entries()),
              lastNodesUpdated: [...nodesUpdated],
            };

            controller.enqueue(`data: ${JSON.stringify(serializedData)}\n\n`);
            isProcessing = false;
          } catch (e) {
            controller.error(e);
            isProcessing = false;
          }
        }, 100);

        rl.on("line", (line: string) => {
          if (!line) {
            return;
          }

          eventBuffer.push(line);
        });

        rl.on("close", () => {
          simulationDone = true;
          console.log("closed");
        });

        rl.on("error", (error) => {
          controller.error(error);
        });
      },
    });

    return new NextResponse(stream, {
      headers: {
        "Content-Type": "text/event-stream",
        "Cache-Control": "no-cache",
        Connection: "keep-alive",
      },
    });
  } catch (e) {
    return new NextResponse(null, {
      status: 500,
      statusText: (e as Error)?.message,
    });
  }
}
