import {
  IServerMessage,
  EMessageType,
  ITransformedNodeMap,
} from "@/components/Sim/types";
import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
  ISimulationBlock,
  ISimulationEndorsementBlock,
  ISimulationIntermediateInputBlock,
  ISimulationIntermediateEndorsementBlock,
  ISimulationIntermediateDataState,
  VisualizedMessage,
  ActivityAction,
} from "@/contexts/SimContext/types";

// Helper functions
const updateLastActivity = (
  nodeStats: Map<string, ISimulationAggregatedData>,
  nodeId: string,
  type: VisualizedMessage,
  action: ActivityAction,
  time: number,
) => {
  const stats = nodeStats.get(nodeId);
  if (stats) {
    // Always update if it's an EB activity, or if timestamp is newer
    if (
      !stats.lastActivity ||
      type === VisualizedMessage.EB ||
      time >= stats.lastActivity.time
    ) {
      stats.lastActivity = { type, action, time };
    }
  }
};

// Helper function to get latency between two nodes from topology
const getTopologyLatency = (
  topology: ITransformedNodeMap,
  sender: string,
  recipient: string,
): number | null => {
  if (!topology || !topology.links) return null;

  // Create link key in same format as topology loading (sorted)
  const linkIds = [sender, recipient].sort();
  const linkKey = `${linkIds[0]}|${linkIds[1]}`;

  const link = topology.links.get(linkKey);
  return link?.latencyMs ? link.latencyMs / 1000 : null; // Convert ms to seconds
};

const createMessageAnimation = (
  result: ISimulationAggregatedDataState,
  messageType: VisualizedMessage,
  messageId: string,
  sender: string,
  recipient: string,
  sentTime: number,
  targetTime: number,
  fallbackTravelTime: number,
  topology: ITransformedNodeMap,
) => {
  // Try to get realistic latency from topology, fallback to hardcoded time
  const topologyLatency = getTopologyLatency(topology, sender, recipient);
  const travelTime =
    topologyLatency !== null ? topologyLatency : fallbackTravelTime;

  const estimatedReceiveTime = sentTime + travelTime;

  // Only show if message is currently in transit at targetTime
  if (targetTime >= sentTime && targetTime < estimatedReceiveTime) {
    const progress = (targetTime - sentTime) / travelTime;
    const animationKey = `${messageId}-${sender}-${recipient}`;

    result.messages.push({
      id: animationKey,
      type: messageType,
      sender,
      recipient,
      sentTime,
      receivedTime: estimatedReceiveTime,
      progress,
    });
  }
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

// Compute complete aggregated data from timeline events up to a specific time
export const computeAggregatedDataAtTime = (
  events: IServerMessage[],
  targetTime: number,
  nodeIds: string[],
  topology: ITransformedNodeMap,
): ISimulationAggregatedDataState => {
  const nodeStats = new Map<string, ISimulationAggregatedData>();

  // Initialize stats for all nodes
  nodeIds.forEach((nodeId) => {
    nodeStats.set(nodeId, {
      bytesSent: 0,
      bytesReceived: 0,
      generated: {},
      sent: {},
      received: {},
    });
  });

  // Initialize intermediate state for tracking relationships between events
  const intermediate: ISimulationIntermediateDataState = {
    txs: [],
    txStatuses: [],
    praosTxs: new Set<number>(),
    leiosTxs: new Set<number>(),
    ibs: new Map<string, ISimulationIntermediateInputBlock>(),
    ebs: new Map<string, ISimulationIntermediateEndorsementBlock>(),
    bytes: new Map<string, number>(),
  };

  // Initialize result structure
  // REVIEW: migrated from old processMessage workflow. Is this still needed?
  const result: ISimulationAggregatedDataState = {
    progress: targetTime,
    nodes: nodeStats,
    global: {
      praosTxOnChain: 0,
      leiosTxOnChain: 0,
    },
    blocks: [],
    transactions: [],
    lastNodesUpdated: [],
    messages: [],
    // Add event counts for the UI
    eventCounts: {
      total: 0,
      byType: {},
    },
  };

  // Process all timeline events up to the target time
  const filteredEvents = events.filter((event) => event.time_s <= targetTime);

  // Update event counts
  result.eventCounts.total = filteredEvents.length;
  for (const event of filteredEvents) {
    const type = event.message.type;
    result.eventCounts.byType[type] =
      (result.eventCounts.byType[type] || 0) + 1;
  }

  for (const event of filteredEvents) {
    const { message } = event;

    switch (message.type) {
      case EMessageType.TransactionGenerated: {
        intermediate.txStatuses[Number(message.id)] = "created";
        const stats = nodeStats.get(message.publisher);
        if (stats) {
          stats.generated["tx"] = (stats.generated["tx"] || 0) + 1;
          intermediate.bytes.set(`tx-${message.id}`, message.size_bytes);
        }
        intermediate.txs.push({
          id: Number(message.id),
          bytes: message.size_bytes,
        });
        break;
      }

      case EMessageType.TransactionSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const bytes = intermediate.bytes.get(`tx-${message.id}`) || 0;
          if (!stats.sent["tx"]) {
            stats.sent["tx"] = { count: 0, bytes: 0 };
          }
          stats.sent["tx"].count += 1;
          stats.sent["tx"].bytes += bytes;
          stats.bytesSent += bytes;
        }

        // Create transaction animation with topology latency
        createMessageAnimation(
          result,
          VisualizedMessage.TX,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          0.05, // fallback travel time for transactions (faster than blocks)
          topology,
        );
        break;
      }

      case EMessageType.TransactionReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const bytes = intermediate.bytes.get(`tx-${message.id}`) || 0;
          if (!stats.received["tx"]) {
            stats.received["tx"] = { count: 0, bytes: 0 };
          }
          stats.received["tx"].count += 1;
          stats.received["tx"].bytes += bytes;
          stats.bytesReceived += bytes;
        }
        break;
      }

      case EMessageType.IBGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated["ib"] = (stats.generated["ib"] || 0) + 1;
          intermediate.bytes.set(`ib-${message.id}`, message.size_bytes);
        }
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
        break;
      }

      case EMessageType.IBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const bytes = intermediate.bytes.get(`ib-${message.id}`) || 0;
          if (!stats.sent["ib"]) {
            stats.sent["ib"] = { count: 0, bytes: 0 };
          }
          stats.sent["ib"].count += 1;
          stats.sent["ib"].bytes += bytes;
          stats.bytesSent += bytes;
        }
        break;
      }

      case EMessageType.IBReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const bytes = intermediate.bytes.get(`ib-${message.id}`) || 0;
          if (!stats.received["ib"]) {
            stats.received["ib"] = { count: 0, bytes: 0 };
          }
          stats.received["ib"].count += 1;
          stats.received["ib"].bytes += bytes;
          stats.bytesReceived += bytes;
        }
        break;
      }

      case EMessageType.EBGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated["eb"] = (stats.generated["eb"] || 0) + 1;
          intermediate.bytes.set(`eb-${message.id}`, message.size_bytes);
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.producer,
          VisualizedMessage.EB,
          ActivityAction.Generated,
          event.time_s,
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
        break;
      }

      case EMessageType.EBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const bytes = intermediate.bytes.get(`eb-${message.id}`) || 0;
          if (!stats.sent["eb"]) {
            stats.sent["eb"] = { count: 0, bytes: 0 };
          }
          stats.sent["eb"].count += 1;
          stats.sent["eb"].bytes += bytes;
          stats.bytesSent += bytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.sender,
          VisualizedMessage.EB,
          ActivityAction.Sent,
          event.time_s,
        );

        // Create animation with topology latency
        createMessageAnimation(
          result,
          VisualizedMessage.EB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          1.0, // fallback travel time for EB
          topology,
        );
        break;
      }

      case EMessageType.EBReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const bytes = intermediate.bytes.get(`eb-${message.id}`) || 0;
          if (!stats.received["eb"]) {
            stats.received["eb"] = { count: 0, bytes: 0 };
          }
          stats.received["eb"].count += 1;
          stats.received["eb"].bytes += bytes;
          stats.bytesReceived += bytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.recipient,
          VisualizedMessage.EB,
          ActivityAction.Received,
          event.time_s,
        );
        break;
      }

      case EMessageType.RBGenerated: {
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
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated["pb"] = (stats.generated["pb"] || 0) + 1;
          intermediate.bytes.set(`pb-${message.id}`, message.size_bytes);
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.producer,
          VisualizedMessage.RB,
          ActivityAction.Generated,
          event.time_s,
        );

        result.global.praosTxOnChain = intermediate.praosTxs.size;
        result.global.leiosTxOnChain = intermediate.leiosTxs.size;
        result.blocks.push(block);
        break;
      }

      case EMessageType.RBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const bytes = intermediate.bytes.get(`pb-${message.id}`) || 0;
          if (!stats.sent["pb"]) {
            stats.sent["pb"] = { count: 0, bytes: 0 };
          }
          stats.sent["pb"].count += 1;
          stats.sent["pb"].bytes += bytes;
          stats.bytesSent += bytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.sender,
          VisualizedMessage.RB,
          ActivityAction.Sent,
          event.time_s,
        );

        // Create RB animation with topology latency
        createMessageAnimation(
          result,
          VisualizedMessage.RB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          0.1, // fallback travel time for RB
          topology,
        );
        break;
      }

      case EMessageType.RBReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const bytes = intermediate.bytes.get(`pb-${message.id}`) || 0;
          if (!stats.received["pb"]) {
            stats.received["pb"] = { count: 0, bytes: 0 };
          }
          stats.received["pb"].count += 1;
          stats.received["pb"].bytes += bytes;
          stats.bytesReceived += bytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.recipient,
          VisualizedMessage.RB,
          ActivityAction.Received,
          event.time_s,
        );
        break;
      }

      case EMessageType.VTBundleGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated["votes"] = (stats.generated["votes"] || 0) + 1;
          intermediate.bytes.set(`votes-${message.id}`, message.size_bytes);
        }
        break;
      }

      case EMessageType.VTBundleSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const bytes = intermediate.bytes.get(`votes-${message.id}`) || 0;
          if (!stats.sent["votes"]) {
            stats.sent["votes"] = { count: 0, bytes: 0 };
          }
          stats.sent["votes"].count += 1;
          stats.sent["votes"].bytes += bytes;
          stats.bytesSent += bytes;
        }
        break;
      }

      case EMessageType.VTBundleReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const bytes = intermediate.bytes.get(`votes-${message.id}`) || 0;
          if (!stats.received["votes"]) {
            stats.received["votes"] = { count: 0, bytes: 0 };
          }
          stats.received["votes"].count += 1;
          stats.received["votes"].bytes += bytes;
          stats.bytesReceived += bytes;
        }
        break;
      }
    }
  }

  return result;
};
