import { createReadStream, statSync } from "fs";
import { NextResponse } from "next/server";
import readline from 'readline';

import { EMessageType, IServerMessage } from "@/components/Graph/types";
import { messagesPath } from "../../utils";

const MESSAGE_BUFFER_IN_MS = 200;

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

function getTimestampAtPosition(filePath: string, position: number): Promise<number> {
  return new Promise((resolve, reject) => {
    const stream = createReadStream(filePath, { start: position });
    let foundNewLine = false;
    let adjustedPosition = position;

    // Read a few bytes to find the newline character
    stream.on('data', (chunk) => {
      const decoded = chunk.toString("utf8");
      for (let i = 0; i < decoded.length; i++) {
        if (decoded[i] === '\n') {
          foundNewLine = true;
          adjustedPosition += i + 1; // Move to the start of the next line
          break;
        }
      }

      stream.close(); // Stop reading once the newline is found
    });

    stream.on('close', () => {
      if (foundNewLine) {
        // Now use readline to get the timestamp from the new line
        const lineStream = createReadStream(filePath, { start: adjustedPosition });
        const rl = readline.createInterface({
          input: lineStream,
          crlfDelay: Infinity,
        });

        rl.on('line', (line) => {
          const message: IServerMessage = JSON.parse(line);
          const timestamp = message.time / 1_000_000;
          rl.close();
          resolve(timestamp);
        });

        rl.on('error', (err) => {
          reject(err);
        });
      } else {
        reject(new Error("Could not find a newline character in the provided range"));
      }
    });

    stream.on('error', (err) => {
      reject(err);
    });
  });
}

export async function GET(req: Request) {
  try {
    const url = new URL(req.url);
    const currentTime = parseInt(url.searchParams.get("time") || "", 10);

    if (isNaN(currentTime)) {
      return new NextResponse("Invalid currentTime parameter", { status: 400 });
    }

    const startPosition = await findStartPosition(messagesPath, currentTime);
    const fileStream = createReadStream(messagesPath, { encoding: "utf8", start: startPosition });
    const rl = readline.createInterface({
      input: fileStream,
      crlfDelay: Infinity
    })
    
    const stream = new ReadableStream({
      start(controller) {
        rl.on("line", (line) => {
          try {
            const message: IServerMessage = JSON.parse(line);
            const aboveLowerLimit = message.time / 1_000_000 >= currentTime;
            const underUpperLimit = message.time / 1_000_000 < currentTime + MESSAGE_BUFFER_IN_MS;
  
            // Check if the message falls within the time range
            if (aboveLowerLimit && underUpperLimit && [EMessageType.TransactionGenerated, EMessageType.TransactionReceived, EMessageType.TransactionSent].includes(message.message.type)) {
              controller.enqueue(new TextEncoder().encode(JSON.stringify(message) + "\n"));
            }

            // Free up resources if we're already pass the buffer window.
            if (message.time / 1_000_000 >= currentTime + MESSAGE_BUFFER_IN_MS) {
              rl.close();
              fileStream.destroy();
            }
          } catch (error) {
            // Handle JSON parse errors or other issues
            controller.error(error);
          }
        });
  
        rl.on("close", () => {
          controller.close();
        });
  
        rl.on("error", (error) => {
          controller.error(error);
        });
      }
    });

    // const stream = new ReadableStream(
    //   {
    //     start(controller) {
    //       start = performance.now();
    //       fileStream.on("data", (chunk) => {
    //         buffer += chunk;
    //         let lines = buffer.split("\n");
    //         buffer = lines.pop() || ""; // Keep the last incomplete line
  
    //         for (const line of lines) {
    //           if (!line.trim()) continue;
  
    //           try {
    //             const message: IServerMessage = JSON.parse(line);
    //             const aboveLowerLimit = message.time / 1_000_000 >= currentTime - halfRange;
    //             const underUpperLimit = message.time / 1_000_000 < currentTime + halfRange;
  
    //             // Check if the message falls within the time range
    //             if (aboveLowerLimit && underUpperLimit && !sent) {
    //               // Stream the message if it matches the time range
    //               controller.enqueue(new TextEncoder().encode(JSON.stringify(message) + "\n"));
    //               sent = true;
    //             }
    //           } catch (error) {
    //             console.error("Error parsing JSON line:", error);
    //             controller.error(new Error("Error parsing JSON line"));
    //             fileStream.destroy();
    //             break;
    //           }
    //         }
    //       });

    //       fileStream.on("end", () => {
    //         end = performance.now();
    //         console.log(end - start);
    //         if (buffer.trim()) {
    //           try {
    //             const message = JSON.parse(buffer); // Parse the last incomplete line
    //             controller.enqueue(
    //               new TextEncoder().encode(JSON.stringify(message) + "\n"),
    //             );
    //           } catch (error) {
    //             console.error("Error parsing final JSON line:", error);
    //             controller.error(new Error("Error parsing final JSON line"));
    //           }
    //         }
    //         controller.close();
    //       });

    //       fileStream.on("error", (error) => {
    //         console.error("File stream error:", error);
    //         controller.error(new Error("File stream error"));
    //       });
    //     },
    //   },
    //   {
    //     highWaterMark: 100_000,
    //   },
    // );

    // Return a streaming response
    return new NextResponse(stream, {
      headers: {
        "Content-Type": "application/jsonl",
        "Transfer-Encoding": "chunked",
      },
    });
  } catch (e) {
    return new NextResponse(null, {
      status: 500,
      statusText: (e as Error)?.message,
    });
  }
}
