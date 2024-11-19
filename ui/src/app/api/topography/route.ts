import { parse } from "@iarna/toml";
import { createReadStream } from 'fs';
import { NextResponse } from 'next/server';
import path from 'path';

import { ILink, INode, TServerNodeMap } from "@/components/Graph/types";
 
export async function GET(req: Request) {
  try {
    const filePath = path.resolve(__dirname, "../../../../../../../sim-rs/test_data/realistic.toml");
    const fileStream = createReadStream(filePath, { encoding: "utf8", highWaterMark: 100_000 });
    const result = await parse.stream(fileStream) as unknown as { links: ILink[]; nodes: INode[] };
    
    // Create a Readable stream to send data in chunks
    const stream = new ReadableStream({
      start(controller) {
        for (const node of result.nodes) {
          controller.enqueue(new TextEncoder().encode(JSON.stringify({ type: "node", data: node } as TServerNodeMap)))
        }
  
        for (const link of result.links) {
          controller.enqueue(new TextEncoder().encode(JSON.stringify({ type: "link", data: link } as TServerNodeMap)))
        }
  
        controller.close(); // Close the stream when done
      },
    });

    // Return a streaming response
    return new NextResponse(stream, {
      headers: {
        'Content-Type': 'application/jsonl',
        'Transfer-Encoding': 'chunked',
      },
    });
  } catch (e) {
    return new NextResponse(null, {
      status: 500,
      statusText: (e as Error)?.message
    })
  }
}
