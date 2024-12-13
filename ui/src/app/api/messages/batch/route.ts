import { createReadStream } from "fs";
import { NextResponse } from "next/server";
import readline from "readline";

import { getSetSimulationMaxTime } from "@/app/queries";
import { IServerMessage } from "@/components/Graph/types";
import { ISimulationAggregatedDataState } from "@/contexts/GraphContext/types";
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
    const maxTime = await getSetSimulationMaxTime();

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
        };

        interval = setInterval(() => {
          if (eventBuffer.length === 0 && simulationDone) {
            clearInterval(interval);
            rl.close();
            fileStream.close();
            controller.close();
            return;
          }

          try {
            // Process 10k events at a time.
            for (const line of eventBuffer.splice(0, 10000)) {
              const data: IServerMessage = JSON.parse(line);
              processMessage(data, aggregatedData);
            }

            const nextTime = eventBuffer.length > 0 ? JSON.parse(eventBuffer[0]).time / 1_000_000 : maxTime;
            const progress = nextTime / maxTime;
            const serializedData = {
              ...aggregatedData,
              progress,
              nodes: Array.from(aggregatedData.nodes.entries()),
            };

            controller.enqueue(`data: ${JSON.stringify(serializedData)}\n\n`);
          } catch (e) {
            controller.error(e);
          }
        }, 100);

        rl.on("line", (line: string) => {
          try {
            eventBuffer.push(line);
          } catch (error) {
            controller.error(error);
          }
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
