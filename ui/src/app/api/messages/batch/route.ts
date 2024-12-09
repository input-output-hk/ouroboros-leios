import { createReadStream, statSync } from "fs";
import { NextResponse } from "next/server";
import readline from "readline";

import { IServerMessage } from "@/components/Graph/types";
import { messagesPath } from "../../utils";

async function findStartPosition(filePath: string, targetTimestamp: number) {
  const fileSize = statSync(filePath).size;
  let left = 0;
  let right = fileSize;
  let bestPosition = 0;

  while (left <= right) {
    const middle = Math.floor((left + right) / 2);
    const timestampAtMiddle = await getTimestampAtPosition(filePath, middle);

    if (timestampAtMiddle < targetTimestamp) {
      left = middle + 1;
    } else {
      bestPosition = middle;
      right = middle - 1;
    }
  }

  return bestPosition;
}

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
    const startTime = parseInt(url.searchParams.get("startTime") || "");
    const speed = parseInt(url.searchParams.get("speed") || "");

    if (isNaN(startTime)) {
      return new NextResponse(null, { status: 400, statusText: "Invalid currentTime parameter" });
    }

    if (isNaN(speed)) {
      return new NextResponse(null, { status: 400, statusText: "Invalid speed parameter" });
    }

    const startPosition = await findStartPosition(messagesPath, startTime);    
    const fileStream = createReadStream(messagesPath, {
      encoding: "utf8",
      start: startPosition,
    });
    const rl = readline.createInterface({
      input: fileStream,
      crlfDelay: Infinity,
    });

    let initialEventTime: number | null = null;
    let interval: Timer | undefined;
    const startTimeOnServer = performance.now();
    const eventBuffer: { line: string; timeToSend: number }[] = [];
    let rlClosed = false;

    const stream = new ReadableStream({
      cancel() {
        clearInterval(interval);
        rl.close();
      },

      start(controller) {
        const processEventBuffer = () => {
          const now = performance.now();

          while (eventBuffer.length > 0) {
            const { line, timeToSend } = eventBuffer[0];
            if (timeToSend <= now) {
              // Send the event to the client
              controller.enqueue(`data: ${line}\n\n`);
              eventBuffer.shift();
            } else {
              // Next event isn't ready yet
              break;
            }
          }

          // Close the stream if all events have been sent and the file has been fully read
          if (eventBuffer.length === 0 && rlClosed) {
            clearInterval(interval);
            controller.close();
          }
        };

        interval = setInterval(processEventBuffer, 50);

        const processLine = (line: string) => {
          try {
            const message: IServerMessage = JSON.parse(line);
            const eventTime = message.time; // Timestamp in nanoseconds

            if (initialEventTime === null) {
              initialEventTime = eventTime;
            }

            const deltaTime = eventTime - initialEventTime; // Difference in nanoseconds
            const adjustedDelay = (deltaTime / 1_000_000) * speed; // Convert to ms and apply multiplier

            const timeToSend = startTimeOnServer + adjustedDelay;

            eventBuffer.push({ line, timeToSend });
          } catch (error) {
            controller.error(error);
          }
        };

        rl.on("line", (line) => {
          processLine(line);
        });

        rl.on("close", () => {
          console.log('rl closed')
        });

        rl.on("error", (error) => {
          controller.error(error);
          console.log('rl error')
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
