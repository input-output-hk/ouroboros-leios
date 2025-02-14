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
            value.message.type === EMessageType.EndorserBlockGenerated ||
            value.message.type === EMessageType.InputBlockGenerated ||
            value.message.type === EMessageType.PraosBlockGenerated ||
            value.message.type === EMessageType.TransactionGenerated
          ) {
            nodesUpdated.add(value.message.id);
          } else if (
            value.message.type === EMessageType.EndorserBlockReceived ||
            value.message.type === EMessageType.InputBlockReceived ||
            value.message.type === EMessageType.PraosBlockReceived ||
            value.message.type === EMessageType.VotesReceived ||
            value.message.type === EMessageType.TransactionReceived
          ) {
            nodesUpdated.add(value.message.recipient.toString())
          } else if (
            value.message.type === EMessageType.EndorserBlockSent ||
            value.message.type === EMessageType.InputBlockSent ||
            value.message.type === EMessageType.PraosBlockSent ||
            value.message.type === EMessageType.VotesSent ||
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
            progress: batch[batch.length - 1].time,
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
