import { parse } from "@iarna/toml";
import { createReadStream } from 'fs';
import { NextResponse } from 'next/server';
import path from 'path';

import { ILink, INode } from "@/components/Graph/types";
 
export async function GET(req: Request) {
  try {
    const filePath = path.resolve(__dirname, "../../../../../../../sim-rs/test_data/realistic.toml");
    const fileStream = createReadStream(filePath, { encoding: "utf8", highWaterMark: 100_000 });
    const result = await parse.stream(fileStream) as unknown as { links: ILink[]; nodes: INode[] };

    // Return a streaming response
    return NextResponse.json(result);
  } catch (e) {
    return new NextResponse(null, {
      status: 500,
      statusText: (e as Error)?.message
    })
  }
}
