import { EMessageType, IServerMessage } from "@/components/Sim/types";
import { createReadStream, statSync } from "fs";
import readline from "readline";

import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
  ISimulationBlock,
  ISimulationIntermediateDataState,
} from "@/contexts/SimContext/types";

export const incrementNodeAggregationData = (
  aggregationNodeDataRef: ISimulationAggregatedDataState["nodes"],
  id: string,
  key: keyof ISimulationAggregatedData,
) => {
  const matchingNode = aggregationNodeDataRef.get(id);
  aggregationNodeDataRef.set(id, {
    ebGenerated: 0,
    ebReceived: 0,
    ebSent: 0,
    ibGenerated: 0,
    ibReceived: 0,
    ibSent: 0,
    pbGenerated: 0,
    pbReceived: 0,
    pbSent: 0,
    txGenerated: 0,
    txReceived: 0,
    txSent: 0,
    votesGenerated: 0,
    votesReceived: 0,
    votesSent: 0,
    ...matchingNode,
    [key]: (matchingNode?.[key] || 0) + 1,
  });
};

export const processMessage = (
  json: IServerMessage,
  aggregatedData: ISimulationAggregatedDataState,
  intermediate: ISimulationIntermediateDataState,
) => {
  const { message } = json;

  if (message.type === EMessageType.TransactionGenerated) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.publisher.toString(),
      "txGenerated",
    );
    intermediate.txs.push({ id: Number(message.id), bytes: message.bytes });
  } else if (message.type === EMessageType.TransactionSent) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.sender.toString(),
      "txSent",
    );
  } else if (message.type === EMessageType.TransactionReceived) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.recipient.toString(),
      "txReceived",
    );
  } else if (message.type === EMessageType.InputBlockGenerated) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.producer.toString(),
      "ibGenerated",
    );
    intermediate.ibs.set(message.id, {
      slot: message.slot,
      txs: message.transactions,
    });
  } else if (message.type === EMessageType.InputBlockSent) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.sender.toString(),
      "ibSent",
    );
  } else if (message.type === EMessageType.InputBlockReceived) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.recipient.toString(),
      "ibReceived",
    );
  } else if (message.type === EMessageType.PraosBlockGenerated) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.producer.toString(),
      "pbGenerated",
    );
    const block: ISimulationBlock = {
      slot: message.slot,
      txs: message.transactions.map(id => intermediate.txs[id]),
      endorsement: null,
    };
    const praosTx = message.transactions.length;
    let leiosTx = 0;
    if (message.endorsement != null) {
      const ebId = message.endorsement.eb.id;
      const eb = intermediate.ebs.get(ebId)!;
      const ibs = eb.ibs.map(id => {
        const ib = intermediate.ibs.get(id)!;
        leiosTx += ib.txs.length;
        const txs = ib.txs.map(tx => intermediate.txs[tx]);
        return {
          id,
          slot: ib.slot,
          txs,
        };
      })
      block.endorsement = {
        id: ebId,
        slot: eb.slot,
        ibs,
      }
    }
    aggregatedData.global.praosTxOnChain += praosTx;
    aggregatedData.global.leiosTxOnChain += leiosTx;
    aggregatedData.blocks.push(block);
  } else if (message.type === EMessageType.PraosBlockSent) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.sender.toString(),
      "pbSent",
    );
  } else if (message.type === EMessageType.PraosBlockReceived) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.recipient.toString(),
      "pbReceived",
    );
  } else if (message.type === EMessageType.EndorserBlockGenerated) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.producer.toString(),
      "ebGenerated",
    );
    const ibs = message.input_blocks.map(ib => ib.id);
    intermediate.ebs.set(message.id, {
      slot: message.slot,
      ibs,
    });
  } else if (message.type === EMessageType.EndorserBlockSent) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.sender.toString(),
      "ebSent",
    );
  } else if (message.type === EMessageType.EndorserBlockReceived) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.recipient.toString(),
      "ebReceived",
    );
  } else if (message.type === EMessageType.VotesGenerated) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.id.toString(),
      "votesGenerated",
    );
  } else if (message.type === EMessageType.VotesSent) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.sender.toString(),
      "votesSent",
    );
  } else if (message.type === EMessageType.VotesReceived) {
    incrementNodeAggregationData(
      aggregatedData.nodes,
      message.recipient.toString(),
      "votesReceived",
    );
  }
};

export async function findStartPosition(
  filePath: string,
  targetTimestamp: number,
) {
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

export function getTimestampAtPosition(
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
