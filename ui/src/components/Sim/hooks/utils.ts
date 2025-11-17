import { EMessageType, IServerMessage } from "@/components/Sim/types";

import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
  ISimulationBlock,
  ISimulationEndorsementBlock,
  ISimulationIntermediateDataState,
} from "@/contexts/SimContext/types";

const trackDataGenerated = (
  aggregationNodeDataRef: ISimulationAggregatedDataState,
  intermediate: ISimulationIntermediateDataState,
  nodeId: string,
  type: string,
  id: string,
  bytes: number,
) => {
  const data = getNodeData(aggregationNodeDataRef, nodeId);
  data.generated[type] = (data.generated[type] ?? 0) + 1;
  intermediate.bytes.set(`${type}-${id}`, bytes);
};

const trackDataSent = (
  aggregationNodeDataRef: ISimulationAggregatedDataState,
  intermediate: ISimulationIntermediateDataState,
  nodeId: string,
  type: string,
  id: string,
) => {
  const data = getNodeData(aggregationNodeDataRef, nodeId);
  const bytes = intermediate.bytes.get(`${type}-${id}`) ?? 0;
  if (!data.sent[type]) {
    data.sent[type] = { count: 0, bytes: 0 };
  }
  data.sent[type].count += 1;
  data.sent[type].bytes += bytes;
  data.bytesSent += bytes;
};

const trackDataReceived = (
  aggregationNodeDataRef: ISimulationAggregatedDataState,
  intermediate: ISimulationIntermediateDataState,
  nodeId: string,
  type: string,
  id: string,
) => {
  const data = getNodeData(aggregationNodeDataRef, nodeId);
  const bytes = intermediate.bytes.get(`${type}-${id}`) ?? 0;
  if (!data.received[type]) {
    data.received[type] = { count: 0, bytes: 0 };
  }
  data.received[type].count += 1;
  data.received[type].bytes += bytes;
  data.bytesReceived += bytes;
};

const getNodeData = (
  aggregationNodeDataRef: ISimulationAggregatedDataState,
  nodeId: string,
): ISimulationAggregatedData => {
  let oldData = aggregationNodeDataRef.nodes.get(nodeId);
  if (oldData) {
    return oldData;
  }
  const data = {
    bytesSent: 0,
    bytesReceived: 0,
    generated: {},
    sent: {},
    received: {},
  };
  aggregationNodeDataRef.nodes.set(nodeId, data);
  return data;
};

const extractEb = (
  intermediate: ISimulationIntermediateDataState,
  ebId: string,
): ISimulationEndorsementBlock => {
  const eb = intermediate.ebs.get(ebId)!;
  const txs = eb.txs.map((id) => intermediate.txs[Number(id)]);
  const ibs = eb.ibs.map((id) => {
    const ib = intermediate.ibs.get(id)!;
    for (const tx of ib.txs) {
      if (!intermediate.praosTxs.has(tx)) {
        intermediate.leiosTxs.add(tx);
        intermediate.txStatuses[tx] = "onChain";
      }
    }
    const txs = ib.txs.map((tx) => intermediate.txs[tx]);
    return {
      id,
      slot: ib.slot,
      pipeline: ib.pipeline,
      headerBytes: ib.headerBytes,
      txs,
    };
  });
  const ebs = eb.ebs.map((id) => extractEb(intermediate, id));
  return {
    id: ebId,
    slot: eb.slot,
    pipeline: eb.pipeline,
    bytes: eb.bytes,
    txs,
    ibs,
    ebs,
  };
};

// TODO: unsued
export const processMessage = (
  json: IServerMessage,
  aggregatedData: ISimulationAggregatedDataState,
  intermediate: ISimulationIntermediateDataState,
) => {
  const { message } = json;

  if (message.type === EMessageType.TransactionGenerated) {
    intermediate.txStatuses[Number(message.id)] = "created";
    trackDataGenerated(
      aggregatedData,
      intermediate,
      message.publisher,
      "tx",
      message.id,
      message.size_bytes,
    );
    intermediate.txs.push({
      id: Number(message.id),
      bytes: message.size_bytes,
    });
  } else if (message.type === EMessageType.TransactionSent) {
    trackDataSent(
      aggregatedData,
      intermediate,
      message.sender,
      "tx",
      message.id,
    );
  } else if (message.type === EMessageType.TransactionReceived) {
    trackDataReceived(
      aggregatedData,
      intermediate,
      message.recipient,
      "tx",
      message.id,
    );
  } else if (message.type === EMessageType.IBGenerated) {
    trackDataGenerated(
      aggregatedData,
      intermediate,
      message.producer,
      "ib",
      message.id,
      message.size_bytes,
    );
    for (const id of message.transactions) {
      if (intermediate.txStatuses[id] === "created") {
        intermediate.txStatuses[id] = "inIb";
      }
    }
    intermediate.ibs.set(message.id, {
      slot: message.slot,
      pipeline: message.pipeline,
      headerBytes: message.header_bytes,
      txs: message.transactions,
    });
  } else if (message.type === EMessageType.IBSent) {
    trackDataSent(
      aggregatedData,
      intermediate,
      message.sender,
      "ib",
      message.id,
    );
  } else if (message.type === EMessageType.IBReceived) {
    trackDataReceived(
      aggregatedData,
      intermediate,
      message.recipient,
      "ib",
      message.id,
    );
  } else if (message.type === EMessageType.RBGenerated) {
    const block: ISimulationBlock = {
      slot: message.slot,
      headerBytes: message.header_bytes,
      txs: message.transactions.map((id) => intermediate.txs[id]),
      cert: null,
    };
    for (const id of message.transactions) {
      intermediate.praosTxs.add(id);
      intermediate.txStatuses[id] = "onChain";
    }
    if (message.endorsement != null) {
      const ebId = message.endorsement.eb.id;
      block.cert = {
        bytes: message.endorsement.size_bytes,
        eb: extractEb(intermediate, ebId),
      };
    }
    trackDataGenerated(
      aggregatedData,
      intermediate,
      message.producer,
      "pb",
      message.id,
      message.size_bytes,
    );
    aggregatedData.global.praosTxOnChain = intermediate.praosTxs.size;
    aggregatedData.global.leiosTxOnChain = intermediate.leiosTxs.size;
    aggregatedData.blocks.push(block);
  } else if (message.type === EMessageType.RBSent) {
    trackDataSent(
      aggregatedData,
      intermediate,
      message.sender,
      "pb",
      message.id,
    );
  } else if (message.type === EMessageType.RBReceived) {
    trackDataReceived(
      aggregatedData,
      intermediate,
      message.recipient,
      "pb",
      message.id,
    );
  } else if (message.type === EMessageType.EBGenerated) {
    trackDataGenerated(
      aggregatedData,
      intermediate,
      message.producer,
      "eb",
      message.id,
      message.size_bytes,
    );
    for (const { id: ibId } of message.input_blocks) {
      for (const tx of intermediate.ibs.get(ibId)?.txs ?? []) {
        if (
          intermediate.txStatuses[tx] === "created" ||
          intermediate.txStatuses[tx] === "inIb"
        ) {
          intermediate.txStatuses[tx] = "inEb";
        }
      }
    }
    for (const { id: txId } of message.transactions) {
      const tx = Number(txId);
      if (
        intermediate.txStatuses[tx] === "created" ||
        intermediate.txStatuses[tx] === "inIb"
      ) {
        intermediate.txStatuses[tx] = "inEb";
      }
    }
    intermediate.ebs.set(message.id, {
      slot: message.slot,
      pipeline: message.pipeline,
      bytes: message.size_bytes,
      txs: message.transactions.map((tx) => tx.id),
      ibs: message.input_blocks.map((ib) => ib.id),
      ebs: message.endorser_blocks.map((eb) => eb.id),
    });
  } else if (message.type === EMessageType.EBSent) {
    trackDataSent(
      aggregatedData,
      intermediate,
      message.sender,
      "eb",
      message.id,
    );
  } else if (message.type === EMessageType.EBReceived) {
    trackDataReceived(
      aggregatedData,
      intermediate,
      message.recipient,
      "eb",
      message.id,
    );
  } else if (message.type === EMessageType.VTBundleGenerated) {
    trackDataGenerated(
      aggregatedData,
      intermediate,
      message.producer,
      "votes",
      message.id,
      message.size_bytes,
    );
  } else if (message.type === EMessageType.VTBundleSent) {
    trackDataSent(
      aggregatedData,
      intermediate,
      message.sender,
      "votes",
      message.id,
    );
  } else if (message.type === EMessageType.VTBundleReceived) {
    trackDataReceived(
      aggregatedData,
      intermediate,
      message.recipient,
      "votes",
      message.id,
    );
  }
};
