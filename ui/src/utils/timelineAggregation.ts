import {
  IServerMessage,
  EServerMessageType,
  ITransformedNodeMap,
} from "@/components/Sim/types";
import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
  EMessageType,
  ActivityAction,
} from "@/contexts/SimContext/types";

// Helper functions
const updateLastActivity = (
  nodeStats: Map<string, ISimulationAggregatedData>,
  nodeId: string,
  type: EMessageType,
  action: ActivityAction,
  time: number,
) => {
  const stats = nodeStats.get(nodeId);
  if (stats) {
    // Always update if it's an EB activity, or if timestamp is newer
    if (
      !stats.lastActivity ||
      type === EMessageType.EB ||
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
  messageType: EMessageType,
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
      generated: new Map<EMessageType, number>(),
      sent: new Map<EMessageType, { count: number; bytes: number }>(),
      received: new Map<EMessageType, { count: number; bytes: number }>(),
    });
  });

  // Initialize nested map for efficient message size lookup: messageType -> messageId -> size
  const messageBytes = new Map<EMessageType, Map<string, number>>();

  // Helper functions for efficient byte storage/retrieval
  const setMessageBytes = (messageType: EMessageType, messageId: string, size: number) => {
    if (!messageBytes.has(messageType)) {
      messageBytes.set(messageType, new Map());
    }
    messageBytes.get(messageType)!.set(messageId, size);
  };

  const getMessageBytes = (messageType: EMessageType, messageId: string): number => {
    return messageBytes.get(messageType)?.get(messageId) || 0;
  };

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
    lastAggregatedTime: targetTime,
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
      case EServerMessageType.TransactionGenerated: {
        const stats = nodeStats.get(message.publisher);
        if (stats) {
          stats.generated.set(EMessageType.TX, (stats.generated.get(EMessageType.TX) || 0) + 1);
          setMessageBytes(EMessageType.TX, message.id, message.size_bytes);
        }
        break;
      }

      case EServerMessageType.TransactionSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.TX, message.id);
          if (!stats.sent.has(EMessageType.TX)) {
            stats.sent.set(EMessageType.TX, { count: 0, bytes: 0 });
          }
          const sentStats = stats.sent.get(EMessageType.TX)!;
          sentStats.count += 1;
          sentStats.bytes += msgBytes;
          stats.bytesSent += msgBytes;
        }

        // Create transaction animation with topology latency
        createMessageAnimation(
          result,
          EMessageType.TX,
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

      case EServerMessageType.TransactionReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.TX, message.id);
          if (!stats.received.has(EMessageType.TX)) {
            stats.received.set(EMessageType.TX, { count: 0, bytes: 0 });
          }
          const receivedStats = stats.received.get(EMessageType.TX)!;
          receivedStats.count += 1;
          receivedStats.bytes += msgBytes;
          stats.bytesReceived += msgBytes;
        }
        break;
      }




      case EServerMessageType.EBGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated.set(EMessageType.EB, (stats.generated.get(EMessageType.EB) || 0) + 1);
          setMessageBytes(EMessageType.EB, message.id, message.size_bytes);
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.producer,
          EMessageType.EB,
          ActivityAction.Generated,
          event.time_s,
        );
        break;
      }

      case EServerMessageType.EBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.EB, message.id);
          if (!stats.sent.has(EMessageType.EB)) {
            stats.sent.set(EMessageType.EB, { count: 0, bytes: 0 });
          }
          const sentStats = stats.sent.get(EMessageType.EB)!;
          sentStats.count += 1;
          sentStats.bytes += msgBytes;
          stats.bytesSent += msgBytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.sender,
          EMessageType.EB,
          ActivityAction.Sent,
          event.time_s,
        );

        // Create animation with topology latency
        createMessageAnimation(
          result,
          EMessageType.EB,
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

      case EServerMessageType.EBReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.EB, message.id);
          if (!stats.received.has(EMessageType.EB)) {
            stats.received.set(EMessageType.EB, { count: 0, bytes: 0 });
          }
          const receivedStats = stats.received.get(EMessageType.EB)!;
          receivedStats.count += 1;
          receivedStats.bytes += msgBytes;
          stats.bytesReceived += msgBytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.recipient,
          EMessageType.EB,
          ActivityAction.Received,
          event.time_s,
        );
        break;
      }

      case EServerMessageType.RBGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated.set(EMessageType.RB, (stats.generated.get(EMessageType.RB) || 0) + 1);
          setMessageBytes(EMessageType.RB, message.id, message.size_bytes);
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.producer,
          EMessageType.RB,
          ActivityAction.Generated,
          event.time_s,
        );

        break;
      }

      case EServerMessageType.RBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.RB, message.id);
          if (!stats.sent.has(EMessageType.RB)) {
            stats.sent.set(EMessageType.RB, { count: 0, bytes: 0 });
          }
          const sentStats = stats.sent.get(EMessageType.RB)!;
          sentStats.count += 1;
          sentStats.bytes += msgBytes;
          stats.bytesSent += msgBytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.sender,
          EMessageType.RB,
          ActivityAction.Sent,
          event.time_s,
        );

        // Create RB animation with topology latency
        createMessageAnimation(
          result,
          EMessageType.RB,
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

      case EServerMessageType.RBReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.RB, message.id);
          if (!stats.received.has(EMessageType.RB)) {
            stats.received.set(EMessageType.RB, { count: 0, bytes: 0 });
          }
          const receivedStats = stats.received.get(EMessageType.RB)!;
          receivedStats.count += 1;
          receivedStats.bytes += msgBytes;
          stats.bytesReceived += msgBytes;
        }

        // Track last activity for node coloring
        updateLastActivity(
          nodeStats,
          message.recipient,
          EMessageType.RB,
          ActivityAction.Received,
          event.time_s,
        );
        break;
      }

      case EServerMessageType.VTBundleGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated.set(EMessageType.Votes, (stats.generated.get(EMessageType.Votes) || 0) + 1);
          setMessageBytes(EMessageType.Votes, message.id, message.size_bytes);
        }
        break;
      }

      case EServerMessageType.VTBundleSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.Votes, message.id);
          if (!stats.sent.has(EMessageType.Votes)) {
            stats.sent.set(EMessageType.Votes, { count: 0, bytes: 0 });
          }
          const sentStats = stats.sent.get(EMessageType.Votes)!;
          sentStats.count += 1;
          sentStats.bytes += msgBytes;
          stats.bytesSent += msgBytes;
        }

        // Create vote animation with topology latency
        createMessageAnimation(
          result,
          EMessageType.Votes,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          0.2, // fallback travel time for votes
          topology,
        );
        break;
      }

      case EServerMessageType.VTBundleReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          const msgBytes = getMessageBytes(EMessageType.Votes, message.id);
          if (!stats.received.has(EMessageType.Votes)) {
            stats.received.set(EMessageType.Votes, { count: 0, bytes: 0 });
          }
          const receivedStats = stats.received.get(EMessageType.Votes)!;
          receivedStats.count += 1;
          receivedStats.bytes += msgBytes;
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
