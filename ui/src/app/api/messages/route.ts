import { MILLISECOND_RANGE } from "@/components/Graph/Graph";
import { IServerMessage } from "@/components/Graph/types";
import { createReadStream } from "fs";
import { NextResponse } from "next/server";
import path from "path";

export async function GET(req: Request) {
  try {
    const url = new URL(req.url);
    const currentTime = parseInt(url.searchParams.get("time") || "", 10);

    if (isNaN(currentTime)) {
      return new NextResponse("Invalid currentTime parameter", { status: 400 });
    }

    const filePath = path.resolve(
      __dirname,
      "../../../../../../../sim-rs/output/messages.jsonl",
    );
    const fileStream = createReadStream(filePath, { encoding: "utf8" });
    const halfRange = MILLISECOND_RANGE / 2;
    
    let buffer = "";

    const stream = new ReadableStream(
      {
        start(controller) {
          fileStream.on("data", (chunk) => {
            buffer += chunk;
            let lines = buffer.split("\n");
            buffer = lines.pop() || ""; // Keep the last incomplete line
  
            for (const line of lines) {
              if (!line.trim()) continue;
  
              try {
                const message: IServerMessage = JSON.parse(line);
  
                // Check if the message falls within the time range
                if (message.time / 1_000_000 >= currentTime - halfRange && message.time / 1_000_000 < currentTime + halfRange) {
                  // Stream the message if it matches the time range
                  controller.enqueue(new TextEncoder().encode(JSON.stringify(message) + "\n"));
                }
              } catch (error) {
                console.error("Error parsing JSON line:", error);
                controller.error(new Error("Error parsing JSON line"));
                fileStream.destroy();
                break;
              }
            }
          });

          fileStream.on("end", () => {
            if (buffer.trim()) {
              try {
                const message = JSON.parse(buffer); // Parse the last incomplete line
                controller.enqueue(
                  new TextEncoder().encode(JSON.stringify(message) + "\n"),
                );
              } catch (error) {
                console.error("Error parsing final JSON line:", error);
                controller.error(new Error("Error parsing final JSON line"));
              }
            }
            controller.close();
          });

          fileStream.on("error", (error) => {
            console.error("File stream error:", error);
            controller.error(new Error("File stream error"));
          });
        },
      },
      {
        highWaterMark: 100_000,
      },
    );

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
