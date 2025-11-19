import {
  IServerMessage,
  EMessageType,
  ITransformedNodeMap,
} from "@/components/Sim/types";
import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
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

// Memoization cache for topology latency lookups: Map<sender, Map<recipient, latency>>
const latencyCache = new Map<string, Map<string, number | null>>();

// Helper function to get latency between two nodes from topology
const getTopologyLatency = (
  topology: ITransformedNodeMap,
  sender: string,
  recipient: string,
): number | null => {
  if (!topology || !topology.links) return null;

  // Check cache first
  const senderCache = latencyCache.get(sender);
  if (senderCache && senderCache.has(recipient)) {
    return senderCache.get(recipient)!;
  }

  // Compute result - need to check both directions since topology uses sorted keys
  const linkIds = [sender, recipient].sort();
  const linkKey = `${linkIds[0]}|${linkIds[1]}`;
  const link = topology.links.get(linkKey);
  const latency = link?.latencyMs ? link.latencyMs / 1000 : null; // Convert ms to seconds

  // Cache result in both directions for bidirectional access
  if (!latencyCache.has(sender)) {
    latencyCache.set(sender, new Map());
  }
  if (!latencyCache.has(recipient)) {
    latencyCache.set(recipient, new Map());
  }

  latencyCache.get(sender)!.set(recipient, latency);
  latencyCache.get(recipient)!.set(sender, latency);

  return latency;
};

// Clear latency cache when topology changes
export const clearLatencyCache = () => {
  latencyCache.clear();
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

  // Initialize intermediate state for tracking message sizes
  const bytes = new Map<string, number>();

  // Initialize result structure
  const result: ISimulationAggregatedDataState = {
    progress: targetTime,
    nodes: nodeStats,
    global: {
      praosTxOnChain: 0,
      leiosTxOnChain: 0,
    },
    lastNodesUpdated: [],
    messages: [],
    // Add event counts for the UI
    eventCounts: {
      total: 0,
      byType: {},
    },
  };

  // Process timeline events up to target time with early termination
  let eventCount = 0;
  const eventCountsByType: Record<string, number> = {};

  for (const event of events) {
    // Stop processing when we reach target time
    if (event.time_s > targetTime) {
      break;
    }

    const { message } = event;

    // Accumulate event counts
    eventCount++;
    const type = message.type;
    eventCountsByType[type] = (eventCountsByType[type] || 0) + 1;

    switch (message.type) {
      case EMessageType.TransactionGenerated: {
        const stats = nodeStats.get(message.publisher);
        if (stats) {
          stats.generated["tx"] = (stats.generated["tx"] || 0) + 1;
          bytes.set(`tx-${message.id}`, message.size_bytes);
        }
        break;
      }

      case EMessageType.TransactionSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = bytes.get(`tx-${message.id}`) || 0;
          if (!stats.sent["tx"]) {
            stats.sent["tx"] = { count: 0, bytes: 0 };
          }
          stats.sent["tx"].count += 1;
          stats.sent["tx"].bytes += msgBytes;
          stats.bytesSent += msgBytes;
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
          const msgBytes = bytes.get(`tx-${message.id}`) || 0;
          if (!stats.received["tx"]) {
            stats.received["tx"] = { count: 0, bytes: 0 };
          }
          stats.received["tx"].count += 1;
          stats.received["tx"].bytes += msgBytes;
          stats.bytesReceived += msgBytes;
        }
        break;
      }

      case EMessageType.IBGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated["ib"] = (stats.generated["ib"] || 0) + 1;
          bytes.set(`ib-${message.id}`, message.size_bytes);
        }
        break;
      }

      case EMessageType.IBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = bytes.get(`ib-${message.id}`) || 0;
          if (!stats.sent["ib"]) {
            stats.sent["ib"] = { count: 0, bytes: 0 };
          }
          stats.sent["ib"].count += 1;
          stats.sent["ib"].bytes += msgBytes;
          stats.bytesSent += msgBytes;
        }
        break;
      }

      case EMessageType.IBReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const msgBytes = bytes.get(`ib-${message.id}`) || 0;
          if (!stats.received["ib"]) {
            stats.received["ib"] = { count: 0, bytes: 0 };
          }
          stats.received["ib"].count += 1;
          stats.received["ib"].bytes += msgBytes;
          stats.bytesReceived += msgBytes;
        }
        break;
      }

      case EMessageType.EBGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated["eb"] = (stats.generated["eb"] || 0) + 1;
          bytes.set(`eb-${message.id}`, message.size_bytes);
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.producer,
          VisualizedMessage.EB,
          ActivityAction.Generated,
          event.time_s,
        );
        break;
      }

      case EMessageType.EBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = bytes.get(`eb-${message.id}`) || 0;
          if (!stats.sent["eb"]) {
            stats.sent["eb"] = { count: 0, bytes: 0 };
          }
          stats.sent["eb"].count += 1;
          stats.sent["eb"].bytes += msgBytes;
          stats.bytesSent += msgBytes;
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
          const msgBytes = bytes.get(`eb-${message.id}`) || 0;
          if (!stats.received["eb"]) {
            stats.received["eb"] = { count: 0, bytes: 0 };
          }
          stats.received["eb"].count += 1;
          stats.received["eb"].bytes += msgBytes;
          stats.bytesReceived += msgBytes;
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
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated["pb"] = (stats.generated["pb"] || 0) + 1;
          bytes.set(`pb-${message.id}`, message.size_bytes);
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.producer,
          VisualizedMessage.RB,
          ActivityAction.Generated,
          event.time_s,
        );

        break;
      }

      case EMessageType.RBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = bytes.get(`pb-${message.id}`) || 0;
          if (!stats.sent["pb"]) {
            stats.sent["pb"] = { count: 0, bytes: 0 };
          }
          stats.sent["pb"].count += 1;
          stats.sent["pb"].bytes += msgBytes;
          stats.bytesSent += msgBytes;
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
          const msgBytes = bytes.get(`pb-${message.id}`) || 0;
          if (!stats.received["pb"]) {
            stats.received["pb"] = { count: 0, bytes: 0 };
          }
          stats.received["pb"].count += 1;
          stats.received["pb"].bytes += msgBytes;
          stats.bytesReceived += msgBytes;
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
          bytes.set(`votes-${message.id}`, message.size_bytes);
        }
        break;
      }

      case EMessageType.VTBundleSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = bytes.get(`votes-${message.id}`) || 0;
          if (!stats.sent["votes"]) {
            stats.sent["votes"] = { count: 0, bytes: 0 };
          }
          stats.sent["votes"].count += 1;
          stats.sent["votes"].bytes += msgBytes;
          stats.bytesSent += msgBytes;
        }
        break;
      }

      case EMessageType.VTBundleReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const msgBytes = bytes.get(`votes-${message.id}`) || 0;
          if (!stats.received["votes"]) {
            stats.received["votes"] = { count: 0, bytes: 0 };
          }
          stats.received["votes"].count += 1;
          stats.received["votes"].bytes += msgBytes;
          stats.bytesReceived += msgBytes;
        }
        break;
      }
    }
  }

  // Set final event counts
  result.eventCounts.total = eventCount;
  result.eventCounts.byType = eventCountsByType;

  return result;
};
