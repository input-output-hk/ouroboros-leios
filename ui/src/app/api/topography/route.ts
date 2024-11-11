import { parse } from "@iarna/toml";
import { createReadStream } from 'fs';
import { NextResponse } from 'next/server';
import path from 'path';
 
type ResponseData = {
  stream: ReadableStream<Uint8Array<ArrayBufferLike>> | null;
  error?: string;
}

export const dynamic = 'force-static'
 
export async function GET(req: Request) {
  try {
    const filePath = path.resolve(__dirname, "../../../../../../../sim-rs/test_data/small.toml");
    const fileStream = createReadStream(filePath, { encoding: "utf8" });
    // const contents = parse(readFileSync(filePath, { encoding: "utf8" }));
    // const fileStream = new Blob([JSON.stringify(contents.links as any[])]).stream();
    const stream = new ReadableStream({
      start(controller) {
        let buffer = "";
        fileStream.on("data", chunk => {
          buffer += Buffer.from(JSON.stringify(parse(chunk.toString("utf8"))), "utf8");

          let lines = buffer.split(/\n/);
          buffer = lines.pop() || "";
          
          lines.forEach(line => {
            controller.enqueue(new TextEncoder().encode(line + "\n"))
          });
        })

        fileStream.on("end", () => {
          if (buffer.length > 0) {
            controller.enqueue(new TextEncoder().encode(buffer));
          }

          controller.close();
        })

        fileStream.on("error", () => {
          controller.error();
        })
      }
    })

    return new NextResponse<ResponseData>(stream, {
      status: 200,
      headers: {
        "Content-Type": "application/jsonl",
        "Transfer-Encoding": "chunked"
      }
    })
  } catch (e) {
    return new NextResponse(null, {
      status: 500,
      statusText: (e as Error)?.message
    })
  }
}
