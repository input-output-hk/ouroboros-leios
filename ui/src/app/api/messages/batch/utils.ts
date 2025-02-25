import { EMessageType, IServerMessage } from "@/components/Sim/types";

import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
  ISimulationBlock,
  ISimulationIntermediateDataState,
} from "@/contexts/SimContext/types";

const incrementNodeAggregationData = (
  aggregationNodeDataRef: ISimulationAggregatedDataState,
  intermediate: ISimulationIntermediateDataState,
  nodeId: string,
  key: keyof ISimulationAggregatedData,
  id?: string,
) => {
  const matchingNode = aggregationNodeDataRef.nodes.get(nodeId);
  const bytesKey: keyof ISimulationAggregatedData = key.endsWith("Sent") ? "bytesSent" : "bytesReceived";
  aggregationNodeDataRef.nodes.set(nodeId, {
    bytesSent: 0,
    bytesReceived: 0,
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
    [key]: (matchingNode?.[key] ?? 0) + 1,
    [bytesKey]: (matchingNode?.[bytesKey] ?? 0) + (id && intermediate.bytes.get(id) || 0),
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
      aggregatedData,
      intermediate,
      message.publisher.toString(),
      "txGenerated",
    );
    intermediate.bytes.set(`tx-${message.id}`, message.bytes);
    intermediate.txs.push({ id: Number(message.id), bytes: message.bytes });
  } else if (message.type === EMessageType.TransactionSent) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.sender.toString(),
      "txSent",
      `tx-${message.id}`,
    );
  } else if (message.type === EMessageType.TransactionReceived) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.recipient.toString(),
      "txReceived",
      `tx-${message.id}`,
    );
  } else if (message.type === EMessageType.IBGenerated) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.producer.toString(),
      "ibGenerated",
    );
    const bytes = message.transactions.reduce((sum, tx) => sum + (intermediate.bytes.get(`tx-${tx}`) ?? 0), message.header_bytes);
    intermediate.bytes.set(`ib-${message.id}`, bytes)
    intermediate.ibs.set(message.id, {
      slot: message.slot,
      headerBytes: message.header_bytes,
      txs: message.transactions,
    });
  } else if (message.type === EMessageType.IBSent) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.sender.toString(),
      "ibSent",
      `ib-${message.id}`,
    );
  } else if (message.type === EMessageType.IBReceived) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.recipient.toString(),
      "ibReceived",
      `ib-${message.id}`,
    );
  } else if (message.type === EMessageType.RBGenerated) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.producer.toString(),
      "pbGenerated",
    );
    let bytes = message.transactions.reduce((sum, tx) => sum + (intermediate.bytes.get(`tx-${tx}`) ?? 0), message.header_bytes);
    const block: ISimulationBlock = {
      slot: message.slot,
      headerBytes: message.header_bytes,
      txs: message.transactions.map(id => intermediate.txs[id]),
      cert: null,
    };
    for (const id of message.transactions) {
      intermediate.praosTxs.add(id);
    }
    if (message.endorsement != null) {
      bytes += message.endorsement.bytes;
      const ebId = message.endorsement.eb.id;
      const eb = intermediate.ebs.get(ebId)!;
      const ibs = eb.ibs.map(id => {
        const ib = intermediate.ibs.get(id)!;
        for (const tx of ib.txs) {
          if (!intermediate.praosTxs.has(tx)) {
            intermediate.leiosTxs.add(tx);
          }
        }
        const txs = ib.txs.map(tx => intermediate.txs[tx]);
        return {
          id,
          slot: ib.slot,
          headerBytes: ib.headerBytes,
          txs,
        };
      })
      block.cert = {
        bytes: message.endorsement.bytes,
        eb: {
          id: ebId,
          slot: eb.slot,
          bytes: eb.bytes,
          ibs,
        }
      }
    }
    intermediate.bytes.set(`pb-${message.id}`, bytes);
    aggregatedData.global.praosTxOnChain = intermediate.praosTxs.size;
    aggregatedData.global.leiosTxOnChain = intermediate.leiosTxs.size;
    aggregatedData.blocks.push(block);
  } else if (message.type === EMessageType.RBSent) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.sender.toString(),
      "pbSent",
      `pb-${message.id}`,
    );
  } else if (message.type === EMessageType.RBReceived) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.recipient.toString(),
      "pbReceived",
      `pb-${message.id}`,
    );
  } else if (message.type === EMessageType.EBGenerated) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.producer.toString(),
      "ebGenerated",
    );
    const ibs = message.input_blocks.map(ib => ib.id);
    intermediate.bytes.set(`eb-${message.id}`, message.bytes);
    intermediate.ebs.set(message.id, {
      slot: message.slot,
      bytes: message.bytes,
      ibs,
    });
  } else if (message.type === EMessageType.EBSent) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.sender.toString(),
      "ebSent",
      `eb-${message.id}`,
    );
  } else if (message.type === EMessageType.EBReceived) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.recipient.toString(),
      "ebReceived",
      `eb-${message.id}`,
    );
  } else if (message.type === EMessageType.VTBundleGenerated) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.producer.toString(),
      "votesGenerated",
    );
    intermediate.bytes.set(`votes-${message.id}`, message.bytes);
  } else if (message.type === EMessageType.VTBundleSent) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.sender.toString(),
      "votesSent",
      `votes-${message.id}`,
    );
  } else if (message.type === EMessageType.VTBundleReceived) {
    incrementNodeAggregationData(
      aggregatedData,
      intermediate,
      message.recipient.toString(),
      "votesReceived",
      `votes-${message.id}`,
    );
  }
};
