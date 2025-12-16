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
  IMessageTypeCounts,
  INodeActivityState,
} from "@/contexts/SimContext/types";

// Helper functions

// Message type priority order: RBs > EBs > Votes > TXs
const MESSAGE_PRIORITY_ORDER = [
  EMessageType.RB, // Highest priority
  EMessageType.EB,
  EMessageType.Votes,
  EMessageType.TX, // Lowest priority
];

export const getHighestPriorityMessageType = (
  counts: IMessageTypeCounts,
): EMessageType | null => {
  for (const messageType of MESSAGE_PRIORITY_ORDER) {
    if (counts[messageType] > 0) {
      return messageType;
    }
  }
  return null;
};

const createEmptyMessageTypeCounts = (): IMessageTypeCounts => ({
  [EMessageType.RB]: 0,
  [EMessageType.EB]: 0,
  [EMessageType.Votes]: 0,
  [EMessageType.TX]: 0,
});

const getTotalActiveCount = (counts: IMessageTypeCounts): number => {
  return Object.values(counts).reduce((sum, count) => sum + count, 0);
};

// Helper function to update node activity state
const updateNodeActivity = (
  nodeActivityMap: Map<string, INodeActivityState>,
  nodeId: string,
  messageType: EMessageType,
  time: number,
) => {
  const existingActivity = nodeActivityMap.get(nodeId);
  if (existingActivity) {
    // Increment count for this message type
    existingActivity.activeCounts[messageType]++;
    // Update timestamp
    if (time >= existingActivity.lastActivityTime) {
      existingActivity.lastActivityTime = time;
    }
  } else {
    // First activity on this node
    const activeCounts = createEmptyMessageTypeCounts();
    activeCounts[messageType] = 1;
    nodeActivityMap.set(nodeId, {
      lastActivityTime: time,
      activeCounts,
    });
  }
};

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
  travelTime: number,
) => {
  const estimatedReceiveTime = sentTime + travelTime;

  // Create edge key for consistent lookup
  const edgeIds = [sender, recipient].sort();
  const edgeKey = `${edgeIds[0]}|${edgeIds[1]}`;

  // Check if message is currently in transit
  const isInTransit =
    targetTime >= sentTime && targetTime < estimatedReceiveTime;

  if (isInTransit) {
    // Message is traveling - increment reference count and show animation
    const existingEdgeState = result.edges.get(edgeKey);
    if (existingEdgeState) {
      // Increment count for this message type
      existingEdgeState.activeCounts[messageType]++;
      // Update timestamp
      if (sentTime >= existingEdgeState.lastMessageTime) {
        existingEdgeState.lastMessageTime = sentTime;
      }
    } else {
      // First message on this edge
      const activeCounts = createEmptyMessageTypeCounts();
      activeCounts[messageType] = 1;
      result.edges.set(edgeKey, {
        lastMessageTime: sentTime,
        activeCounts,
      });
    }

    // Update node activity for sender and recipient during transit
    updateNodeActivity(result.nodeActivity, sender, messageType, sentTime);
    updateNodeActivity(result.nodeActivity, recipient, messageType, sentTime);

    // Create animation
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
  // Note: We don't handle the "completed" case here since we need to process
  // all messages first to get accurate counts, then clean up afterward
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
  const setMessageBytes = (
    messageType: EMessageType,
    messageId: string,
    size: number,
  ) => {
    if (!messageBytes.has(messageType)) {
      messageBytes.set(messageType, new Map());
    }
    messageBytes.get(messageType)!.set(messageId, size);
  };

  const getMessageBytes = (
    messageType: EMessageType,
    messageId: string,
  ): number => {
    return messageBytes.get(messageType)?.get(messageId) || 0;
  };

  // Initialize result structure
  const result: ISimulationAggregatedDataState = {
    nodes: nodeStats,
    global: {
      praosTxOnChain: 0,
      leiosTxOnChain: 0,
    },
    messages: [],
    edges: new Map(),
    nodeActivity: new Map(),
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
  const MAX_LOOKAHEAD_TIME = 5.0; // seconds

  // Helper function to calculate travel time with 3-tier fallback
  // TODO: take event instead
  const calculateTravelTime = (
    eventIndex: number,
    messageType: EMessageType,
    messageId: string,
    sender: string,
    recipient: string,
    sentTime: number,
    fallbackTime: number,
  ): number => {
    // First: Try to find matching received event
    const receivedTime = findMatchingReceivedEvent(
      eventIndex,
      messageType,
      messageId,
      recipient,
      sentTime,
    );
    if (receivedTime) {
      return receivedTime - sentTime;
    }

    // Second: Try topology latency
    const topologyLatency = getTopologyLatency(topology, sender, recipient);
    if (topologyLatency !== null) {
      return topologyLatency;
    }

    // Third: Use message-type specific fallback
    return fallbackTime;
  };

  // Helper function to look ahead for matching received event within time limit
  // TODO: take event instead
  const findMatchingReceivedEvent = (
    startIndex: number,
    messageType: EMessageType,
    messageId: string,
    recipient: string,
    sentTime: number,
  ): number | null => {
    const maxLookaheadTime = sentTime + MAX_LOOKAHEAD_TIME;

    for (let j = startIndex + 1; j < events.length; j++) {
      const futureEvent = events[j];

      // Stop looking if we've gone beyond our time limit or target time
      if (
        futureEvent.time_s > maxLookaheadTime ||
        futureEvent.time_s > targetTime
      ) {
        break;
      }

      // Check if this is a matching received event
      const isMatchingReceived =
        (messageType === EMessageType.TX &&
          futureEvent.message.type ===
            EServerMessageType.TransactionReceived) ||
        (messageType === EMessageType.EB &&
          futureEvent.message.type === EServerMessageType.EBReceived) ||
        (messageType === EMessageType.RB &&
          futureEvent.message.type === EServerMessageType.RBReceived) ||
        (messageType === EMessageType.Votes &&
          futureEvent.message.type === EServerMessageType.VTBundleReceived);

      if (
        isMatchingReceived &&
        futureEvent.message.id === messageId &&
        futureEvent.message.recipient === recipient &&
        futureEvent.time_s >= sentTime
      ) {
        return futureEvent.time_s; // Return the received time
      }
    }
    return null; // No matching received event found within time window
  };

  for (let i = 0; i < events.length; i++) {
    const event = events[i];
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
          stats.generated.set(
            EMessageType.TX,
            (stats.generated.get(EMessageType.TX) || 0) + 1,
          );
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

        // Calculate travel time with 3-tier fallback
        const travelTime = calculateTravelTime(
          i,
          EMessageType.TX,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          0.05, // fallback for TX
        );

        // Create transaction animation with calculated travel time
        createMessageAnimation(
          result,
          EMessageType.TX,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          travelTime,
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
          stats.generated.set(
            EMessageType.EB,
            (stats.generated.get(EMessageType.EB) || 0) + 1,
          );
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

        // Calculate travel time with 3-tier fallback
        const travelTime = calculateTravelTime(
          i,
          EMessageType.EB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          1.0, // fallback for EB
        );

        // Create animation with calculated travel time
        createMessageAnimation(
          result,
          EMessageType.EB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          travelTime,
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
          stats.generated.set(
            EMessageType.RB,
            (stats.generated.get(EMessageType.RB) || 0) + 1,
          );
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

        // Calculate travel time with 3-tier fallback
        const travelTime = calculateTravelTime(
          i,
          EMessageType.RB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          0.1, // fallback for RB
        );

        // Create RB animation with calculated travel time
        createMessageAnimation(
          result,
          EMessageType.RB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          travelTime,
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
          stats.generated.set(
            EMessageType.Votes,
            (stats.generated.get(EMessageType.Votes) || 0) + 1,
          );
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

        // Calculate travel time with 3-tier fallback
        const travelTime = calculateTravelTime(
          i,
          EMessageType.Votes,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          0.2, // fallback for Votes
        );

        // Create vote animation with calculated travel time
        createMessageAnimation(
          result,
          EMessageType.Votes,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          travelTime,
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

  // Clean up edges with no active messages (revert to default color)
  result.edges.forEach((edgeState, edgeKey) => {
    if (getTotalActiveCount(edgeState.activeCounts) === 0) {
      result.edges.delete(edgeKey);
    }
  });

  // Clean up node activities with no active messages
  result.nodeActivity.forEach((nodeState, nodeId) => {
    if (getTotalActiveCount(nodeState.activeCounts) === 0) {
      result.nodeActivity.delete(nodeId);
    }
  });

  return result;
};
