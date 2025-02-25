import { NextResponse } from "next/server";

import { EMessageType, IServerMessage } from "@/components/Sim/types";
import { ISimulationAggregatedDataState, ISimulationIntermediateDataState } from "@/contexts/SimContext/types";
import { createEventStream, EventStreamReader, messagesPath } from "../../utils";
import { processMessage } from "./utils";

export async function GET(req: Request, res: Response) {
  try {
    const batchSize = new URL(req.url).searchParams.get("batchSize");
    if (isNaN(Number(batchSize))) {
      throw new Error("Invalid batch size.");
    }

    let eventReader: EventStreamReader;

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
      leiosTxs: new Set(),
      praosTxs: new Set(),
      ibs: new Map(),
      ebs: new Map(),
      bytes: new Map(),
    };

    const stream = new ReadableStream({
      start() {
        const eventStream = createEventStream(messagesPath);
        eventReader = eventStream.getReader();
      },
      async pull(controller) {
        const batch: IServerMessage[] = [];
        const nodesUpdated = new Set<string>();

        while (batch.length < Number(batchSize)) {
          const { value, done } = await eventReader.read();
          if (done) {
            break;
          }
          if (
            value.message.type === EMessageType.EBGenerated ||
            value.message.type === EMessageType.IBGenerated ||
            value.message.type === EMessageType.RBGenerated ||
            value.message.type === EMessageType.TransactionGenerated
          ) {
            nodesUpdated.add(value.message.id);
          } else if (
            value.message.type === EMessageType.EBReceived ||
            value.message.type === EMessageType.IBReceived ||
            value.message.type === EMessageType.RBReceived ||
            value.message.type === EMessageType.VTBundleReceived ||
            value.message.type === EMessageType.TransactionReceived
          ) {
            nodesUpdated.add(value.message.recipient.toString())
          } else if (
            value.message.type === EMessageType.EBSent ||
            value.message.type === EMessageType.IBSent ||
            value.message.type === EMessageType.RBSent ||
            value.message.type === EMessageType.VTBundleSent ||
            value.message.type === EMessageType.TransactionSent
          ) {
            nodesUpdated.add(value.message.sender.toString())
          }

          processMessage(value, aggregatedData, intermediate);
          batch.push(value);
        }

        if (batch.length) {
          const serializedData = {
            ...aggregatedData,
            progress: batch[batch.length - 1].time_s,
            nodes: Array.from(aggregatedData.nodes.entries()),
            lastNodesUpdated: [...nodesUpdated],
          };

          controller.enqueue(`data: ${JSON.stringify(serializedData)}\n\n`);
          await new Promise(resolve => setInterval(resolve, 100));
        } else {
          controller.close();
        }
      },
      cancel(reason) {
        eventReader.cancel(reason);
      }
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
