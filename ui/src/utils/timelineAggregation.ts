import {
  IServerMessage,
  EServerMessageType,
  ITransformedNodeMap,
  IVote,
} from "@/components/Sim/types";
import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
  EMessageType,
  ActivityAction,
  IChainState,
  IMessageTypeCounts,
  INodeActivityState,
} from "@/contexts/SimContext/types";

// Helper functions

// Link-colour priority: RB > Announcement > EB > EB txs > Votes.
//
// FIXME: This is a second copy of the order. The one that actually colours
// links lives in Graph/hooks/useHandlers.ts and this export has no importers,
// so the two silently drifted -- this copy was missing Announcement entirely.
// Delete one of them (or have useHandlers import this) so a priority change
// cannot land in the unused half.
const MESSAGE_PRIORITY_ORDER = [
  EMessageType.RB, // Highest priority
  EMessageType.Announcement,
  EMessageType.EB,
  EMessageType.Txs, // EB txs, pulled once the EB is known
  EMessageType.Votes, // Lowest priority
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
  [EMessageType.Txs]: 0,
  [EMessageType.Announcement]: 0,
});

const getTotalActiveCount = (counts: IMessageTypeCounts): number => {
  return Object.values(counts).reduce((sum, count) => sum + count, 0);
};

// Resolve a single Vote to the EB it credits. Prototype votes target the
// announcing RB (`rbHash`) and require the RB to be in the chain to be
// resolvable; simulator and older prototype votes reference the EB directly.
// Returns null when neither path resolves — the caller should defer the
// vote until later (the missing RB/EB may show up in a later event).
const resolveVoteEbId = (chain: IChainState, vote: IVote): string | null => {
  const ebId =
    vote.ebHash ??
    (vote.rbHash ? chain.rbs.get(vote.rbHash)?.announcesEbId : undefined);
  if (!ebId) return null;
  if (!chain.ebs.has(ebId)) return null;
  return ebId;
};

const creditVoteToEb = (chain: IChainState, vote: IVote, ebId: string) => {
  const eb = chain.ebs.get(ebId);
  if (!eb) return;
  eb.voteCount = (eb.voteCount ?? 0) + (vote.weight ?? 1);
  (eb.votes ??= []).push(vote);
};

// Drain pending votes whose RB/EB has since appeared in the chain.
const drainPendingVotes = (chain: IChainState, pending: IVote[]): IVote[] => {
  const stillPending: IVote[] = [];
  for (const v of pending) {
    const ebId = resolveVoteEbId(chain, v);
    if (ebId) creditVoteToEb(chain, v, ebId);
    else stillPending.push(v);
  }
  return stillPending;
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

// Received-time index: `family|id|sender|recipient` -> earliest received time.
// Populated once per ingested batch (same lifecycle as the events array), so
// the per-frame aggregation pass can pair a Sent with its Received by lookup
// instead of scanning ahead through the event array — that scan was quadratic
// in event density and dominated the per-frame cost on vote-heavy runs.
const receivedAtIndex = new Map<string, number>();

const messageFamily = (type: string): string =>
  type.replace(/(Sent|Received)$/, "");

const transitKey = (
  type: string,
  id: string,
  sender: string,
  recipient: string,
): string => `${messageFamily(type)}|${id}|${sender}|${recipient}`;

// Index the Received events of a freshly ingested batch. First write wins:
// duplicate delivery of the same message keeps the earliest arrival, matching
// the old scan-ahead behaviour.
export const indexReceivedEvents = (events: IServerMessage[]) => {
  for (const event of events) {
    const message = event.message as any;
    if (!message.type.endsWith("Received")) continue;
    if (!message.id || !message.sender || !message.recipient) continue;
    const key = transitKey(
      message.type,
      message.id,
      message.sender,
      message.recipient,
    );
    const existing = receivedAtIndex.get(key);
    if (existing === undefined || event.time_s < existing) {
      receivedAtIndex.set(key, event.time_s);
    }
  }
};

// Clear alongside the events array (scenario switch, timeline reset).
export const clearReceivedIndex = () => {
  receivedAtIndex.clear();
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
  sizeBytes: number,
  extra?: { slot?: number; votes?: IVote[]; numTxs?: number },
) => {
  const estimatedReceiveTime = sentTime + travelTime;

  // Create edge key for consistent lookup
  const edgeIds = [sender, recipient].sort();
  const edgeKey = `${edgeIds[0]}|${edgeIds[1]}`;

  // Mark the edge as traversed regardless of whether the message is still in
  // transit at targetTime: an edge that has ever carried a message is drawn
  // solid rather than dotted.
  result.traversedEdges.add(edgeKey);

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
      sizeBytes,
      ...extra,
    });
  }
  // Note: We don't handle the "completed" case here since we need to process
  // all messages first to get accurate counts, then clean up afterward
};

// Message-transit bookkeeping shared by the monotone fold and the window pass.

const MAX_LOOKAHEAD_TIME = 5.0; // seconds

const edgeKeyFor = (a: string, b: string): string => {
  const ids = [a, b].sort();
  return `${ids[0]}|${ids[1]}`;
};

const getMessageParticipants = (
  event: IServerMessage,
): { sender: string; recipient: string } => {
  const { message } = event;
  switch (message.type) {
    case EServerMessageType.TxsSent:
    case EServerMessageType.EBSent:
    case EServerMessageType.RBSent:
    case EServerMessageType.VotesSent:
    case EServerMessageType.AnnouncementSent:
      return {
        sender: (message as any).sender,
        recipient: (message as any).recipient,
      };
    default:
      throw new Error(
        `Cannot extract participants from message type: ${message.type}`,
      );
  }
};

const calculateTravelTime = (
  topology: ITransformedNodeMap,
  event: IServerMessage,
  fallbackTime: number,
): number => {
  const { sender, recipient } = getMessageParticipants(event);
  const sentTime = event.time_s;

  // First: the received-time index built at ingestion. Bounded like the old
  // scan-ahead: a match from the past (a re-send of the same message) or
  // implausibly far out falls through to the estimates below.
  const receivedTime = receivedAtIndex.get(
    transitKey(
      event.message.type,
      (event.message as any).id,
      sender,
      recipient,
    ),
  );
  if (
    receivedTime !== undefined &&
    receivedTime >= sentTime &&
    receivedTime <= sentTime + MAX_LOOKAHEAD_TIME
  ) {
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

// Everything about the aggregate that only ever grows with the playhead and
// is insensitive to event order within the folded prefix: counters, byte
// indices, the chain, and which edges have ever carried a message. This is
// what the resumable fold accumulates; the playhead-dependent remainder
// (in-flight animations, active edge/node counts) is rebuilt per call from
// the trailing MAX_LOOKAHEAD_TIME window.
interface IMonotoneAcc {
  nodeStats: Map<string, ISimulationAggregatedData>;
  chain: IChainState;
  messageBytes: Map<EMessageType, Map<string, number>>;
  traversedEdges: Set<string>;
  eventCount: number;
  eventCountsByType: Record<string, number>;
  // Votes whose target RB / EB hadn't been observed yet when the vote was
  // processed. Re-drained each call so out-of-order arrival (Loki tails each
  // node's stream independently) doesn't silently drop votes from a count.
  pendingVotes: IVote[];
}

const newMonotoneAcc = (nodeIds: string[]): IMonotoneAcc => {
  const nodeStats = new Map<string, ISimulationAggregatedData>();
  nodeIds.forEach((nodeId) => {
    nodeStats.set(nodeId, {
      bytesSent: 0,
      bytesReceived: 0,
      generated: new Map<EMessageType, number>(),
      sent: new Map<EMessageType, { count: number; bytes: number }>(),
      received: new Map<EMessageType, { count: number; bytes: number }>(),
    });
  });
  return {
    nodeStats,
    chain: { rbs: new Map(), ebs: new Map() },
    messageBytes: new Map(),
    traversedEdges: new Set(),
    eventCount: 0,
    eventCountsByType: {},
    pendingVotes: [],
  };
};

// The fold's memo. Forward playback resumes from `index`; a backward seek, a
// change of topology, or a batch merge that touched the folded prefix (the
// object at index-1 is no longer `lastEvent`) discards it and refolds from
// zero. Module-level like the caches above; cleared alongside the events
// array.
let foldCache: {
  index: number;
  targetTime: number;
  lastEvent: IServerMessage | null;
  nodeIdsSig: string;
  acc: IMonotoneAcc;
} | null = null;

export const clearAggregationCache = () => {
  foldCache = null;
};

const setMessageBytes = (
  acc: IMonotoneAcc,
  messageType: EMessageType,
  messageId: string,
  size: number,
) => {
  if (!acc.messageBytes.has(messageType)) {
    acc.messageBytes.set(messageType, new Map());
  }
  acc.messageBytes.get(messageType)!.set(messageId, size);
};

const getMessageBytes = (
  acc: IMonotoneAcc,
  messageType: EMessageType,
  messageId: string,
): number => {
  return acc.messageBytes.get(messageType)?.get(messageId) || 0;
};

// Fold one event into the monotone accumulator. In-transit effects (message
// animations, active edge/node counts) deliberately live elsewhere: a Sent
// event only marks its edge as ever-traversed here.
const foldEvent = (acc: IMonotoneAcc, event: IServerMessage) => {
  const { nodeStats } = acc;
  const { message } = event;

  // Accumulate event counts (use num_txs for txs messages)
  const type = message.type;
  const eventWeight =
    (type === EServerMessageType.TxsSent ||
      type === EServerMessageType.TxsReceived) &&
    "num_txs" in message
      ? (message as any).num_txs || 1
      : 1;
  acc.eventCount += eventWeight;
  acc.eventCountsByType[type] = (acc.eventCountsByType[type] || 0) + eventWeight;

  switch (message.type) {
    case EServerMessageType.TxsGenerated: {
      setMessageBytes(acc, EMessageType.Txs, message.id, message.size_bytes);
      const stats = nodeStats.get(message.publisher);
      if (stats) {
        stats.generated.set(
          EMessageType.Txs,
          (stats.generated.get(EMessageType.Txs) || 0) + 1,
        );
      }
      break;
    }

    case EServerMessageType.TxsSent: {
      const msgBytes = message.msg_size_bytes;
      const numTxs = message.num_txs || 1;
      // Also set on sent so size is available when processing received events
      setMessageBytes(acc, EMessageType.Txs, message.id, msgBytes);
      const stats = nodeStats.get(message.sender);
      if (stats) {
        if (!stats.sent.has(EMessageType.Txs)) {
          stats.sent.set(EMessageType.Txs, { count: 0, bytes: 0 });
        }
        const sentStats = stats.sent.get(EMessageType.Txs)!;
        sentStats.count += numTxs;
        sentStats.bytes += msgBytes;
        stats.bytesSent += msgBytes;
      }
      acc.traversedEdges.add(edgeKeyFor(message.sender, message.recipient));
      break;
    }

    case EServerMessageType.TxsReceived: {
      const numTxs = message.num_txs || 1;
      const stats = nodeStats.get(message.recipient);
      if (stats) {
        const msgBytes = getMessageBytes(acc, EMessageType.Txs, message.id);
        if (!stats.received.has(EMessageType.Txs)) {
          stats.received.set(EMessageType.Txs, { count: 0, bytes: 0 });
        }
        const receivedStats = stats.received.get(EMessageType.Txs)!;
        receivedStats.count += numTxs;
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
        setMessageBytes(acc, EMessageType.EB, message.id, message.size_bytes);
      }

      if (!acc.chain.ebs.has(message.id)) {
        acc.chain.ebs.set(message.id, {
          id: message.id,
          slot: message.slot,
          producer: message.producer,
          sizeBytes: message.size_bytes,
          closureSizeBytes: message.closure_size_bytes,
        });
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
      const msgBytes = getMessageBytes(acc, EMessageType.EB, message.id);
      const stats = nodeStats.get(message.sender);
      if (stats) {
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
      acc.traversedEdges.add(edgeKeyFor(message.sender, message.recipient));
      break;
    }

    case EServerMessageType.EBReceived: {
      const msgBytes = getMessageBytes(acc, EMessageType.EB, message.id);
      const stats = nodeStats.get(message.recipient);
      if (stats) {
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

    case EServerMessageType.AnnouncementSent: {
      const msgBytes = getMessageBytes(
        acc,
        EMessageType.Announcement,
        message.id,
      );
      const stats = nodeStats.get(message.sender);
      if (stats) {
        if (!stats.sent.has(EMessageType.Announcement)) {
          stats.sent.set(EMessageType.Announcement, { count: 0, bytes: 0 });
        }
        const sentStats = stats.sent.get(EMessageType.Announcement)!;
        sentStats.count += 1;
        sentStats.bytes += msgBytes;
        stats.bytesSent += msgBytes;
      }

      // Track last activity for node coloring
      updateLastActivity(
        nodeStats,
        message.sender,
        EMessageType.Announcement,
        ActivityAction.Sent,
        event.time_s,
      );
      acc.traversedEdges.add(edgeKeyFor(message.sender, message.recipient));
      break;
    }

    case EServerMessageType.AnnouncementReceived: {
      const msgBytes = getMessageBytes(
        acc,
        EMessageType.Announcement,
        message.id,
      );
      const stats = nodeStats.get(message.recipient);
      if (stats) {
        if (!stats.received.has(EMessageType.Announcement)) {
          stats.received.set(EMessageType.Announcement, {
            count: 0,
            bytes: 0,
          });
        }
        const receivedStats = stats.received.get(EMessageType.Announcement)!;
        receivedStats.count += 1;
        receivedStats.bytes += msgBytes;
        stats.bytesReceived += msgBytes;
      }

      // Track last activity for node coloring
      updateLastActivity(
        nodeStats,
        message.recipient,
        EMessageType.Announcement,
        ActivityAction.Received,
        event.time_s,
      );
      break;
    }

    case EServerMessageType.RBGenerated: {
      setMessageBytes(acc, EMessageType.RB, message.id, message.size_bytes);
      const stats = nodeStats.get(message.producer);
      if (stats) {
        stats.generated.set(
          EMessageType.RB,
          (stats.generated.get(EMessageType.RB) || 0) + 1,
        );
      }

      if (!acc.chain.rbs.has(message.id)) {
        acc.chain.rbs.set(message.id, {
          id: message.id,
          slot: message.slot,
          blockNumber: message.block_number,
          producer: message.producer,
          sizeBytes: message.size_bytes,
          parentId: message.parent?.id,
          certifiesEbId: message.endorsement?.eb.id,
          announcesEbId: message.announces?.id,
        });
        if (acc.chain.slotZeroTime === undefined) {
          acc.chain.slotZeroTime = event.time_s - message.slot;
        }
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
      const msgBytes = getMessageBytes(acc, EMessageType.RB, message.id);
      const stats = nodeStats.get(message.sender);
      if (stats) {
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
      acc.traversedEdges.add(edgeKeyFor(message.sender, message.recipient));
      break;
    }

    case EServerMessageType.RBReceived: {
      const msgBytes = getMessageBytes(acc, EMessageType.RB, message.id);
      const stats = nodeStats.get(message.recipient);
      if (stats) {
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

    case EServerMessageType.VotesGenerated: {
      setMessageBytes(acc, EMessageType.Votes, message.id, message.size_bytes);
      const stats = nodeStats.get(message.producer);
      if (stats) {
        stats.generated.set(
          EMessageType.Votes,
          (stats.generated.get(EMessageType.Votes) || 0) + 1,
        );
      }
      // Accumulate vote "weight" per EB. The values mean different
      // things across sources but are summed identically; the scenario's
      // `totalVotes` (used in the renderer) normalises to [0,1].
      //
      // Simulator (`{ebId: lottery-hit-count}`): treat lottery hit
      // counts as stake-like weights. For sim-rs defaults the total is
      // 500 (persistent 400 + non-persistent 100).
      //
      // Prototype `Vote[]` may carry `weight` (stake-weighted fraction in
      // [0,1], flattened from a `{numerator,denominator}` rational by the
      // Loki parser — TODO: stabilise the encoding upstream). When
      // present, accumulate the weight; otherwise fall back to 1 per vote
      // (the pre-weights behaviour, which makes sense only if
      // `scenario.totalVotes` is set to the voter count).
      if (Array.isArray(message.votes)) {
        for (const v of message.votes) {
          const ebId = resolveVoteEbId(acc.chain, v);
          if (ebId) creditVoteToEb(acc.chain, v, ebId);
          else acc.pendingVotes.push(v);
        }
      } else {
        for (const [ebId, count] of Object.entries(message.votes)) {
          const eb = acc.chain.ebs.get(ebId);
          if (eb) eb.voteCount = (eb.voteCount ?? 0) + count;
        }
      }
      break;
    }

    case EServerMessageType.VotesSent: {
      const msgBytes = getMessageBytes(acc, EMessageType.Votes, message.id);
      const stats = nodeStats.get(message.sender);
      if (stats) {
        if (!stats.sent.has(EMessageType.Votes)) {
          stats.sent.set(EMessageType.Votes, { count: 0, bytes: 0 });
        }
        const sentStats = stats.sent.get(EMessageType.Votes)!;
        sentStats.count += 1;
        sentStats.bytes += msgBytes;
        stats.bytesSent += msgBytes;
      }
      acc.traversedEdges.add(edgeKeyFor(message.sender, message.recipient));
      break;
    }

    case EServerMessageType.VotesReceived: {
      const msgBytes = getMessageBytes(acc, EMessageType.Votes, message.id);
      const stats = nodeStats.get(message.recipient);
      if (stats) {
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
};

// In-flight messages and the active edge/node counts they imply. Only events
// in (targetTime - MAX_LOOKAHEAD_TIME, targetTime] can still be in transit —
// travel times are bounded by the same constant — so this rescans a bounded
// window per call instead of the whole prefix.
const buildTransitWindow = (
  events: IServerMessage[],
  targetTime: number,
  topology: ITransformedNodeMap,
  acc: IMonotoneAcc,
  result: ISimulationAggregatedDataState,
) => {
  // First event inside the window, by binary search — events are sorted.
  const windowStart = targetTime - MAX_LOOKAHEAD_TIME;
  let lo = 0;
  let hi = events.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (events[mid].time_s <= windowStart) lo = mid + 1;
    else hi = mid;
  }

  for (let i = lo; i < events.length; i++) {
    const event = events[i];
    if (event.time_s > targetTime) break;
    const { message } = event;
    switch (message.type) {
      case EServerMessageType.TxsSent:
        createMessageAnimation(
          result,
          EMessageType.Txs,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          calculateTravelTime(topology, event, 0.05),
          message.msg_size_bytes,
          { numTxs: message.num_txs || 1 },
        );
        break;
      case EServerMessageType.EBSent:
        createMessageAnimation(
          result,
          EMessageType.EB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          calculateTravelTime(topology, event, 1.0),
          getMessageBytes(acc, EMessageType.EB, message.id),
          { slot: message.slot },
        );
        break;
      case EServerMessageType.AnnouncementSent:
        createMessageAnimation(
          result,
          EMessageType.Announcement,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          calculateTravelTime(topology, event, 0.3),
          getMessageBytes(acc, EMessageType.Announcement, message.id),
          { slot: message.slot },
        );
        break;
      case EServerMessageType.RBSent:
        createMessageAnimation(
          result,
          EMessageType.RB,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          calculateTravelTime(topology, event, 0.1),
          getMessageBytes(acc, EMessageType.RB, message.id),
          { slot: message.slot },
        );
        break;
      case EServerMessageType.VotesSent:
        createMessageAnimation(
          result,
          EMessageType.Votes,
          message.id,
          message.sender,
          message.recipient,
          event.time_s,
          targetTime,
          calculateTravelTime(topology, event, 0.2),
          getMessageBytes(acc, EMessageType.Votes, message.id),
          { slot: message.slot, votes: message.votes },
        );
        break;
    }
  }
};

// Per-call copy of the accumulator's node stats: cheap (a dozen nodes, a
// handful of entries each) and keeps returned states from changing under a
// consumer when the fold advances.
const cloneNodeStats = (
  nodeStats: Map<string, ISimulationAggregatedData>,
): Map<string, ISimulationAggregatedData> => {
  const out = new Map<string, ISimulationAggregatedData>();
  for (const [nodeId, stats] of nodeStats) {
    out.set(nodeId, {
      ...stats,
      generated: new Map(stats.generated),
      sent: new Map([...stats.sent].map(([k, v]) => [k, { ...v }])),
      received: new Map([...stats.received].map(([k, v]) => [k, { ...v }])),
    });
  }
  return out;
};

// Compute complete aggregated data from timeline events up to a specific time.
//
// Memoized for the playback direction that matters: moving forward resumes
// the monotone fold from the cached cursor and only rescans the trailing
// transit window, so a 60 Hz tick costs O(new events + window) instead of
// O(everything since slot zero). Seeking backwards, switching topology, or a
// batch merge that rewrote the folded prefix falls back to a full recompute
// (which re-primes the cache).
//
// The returned chain maps are fresh per call but share row objects with the
// accumulator; a row's voteCount can therefore keep growing after the state
// was returned. Consumers read values on render, so this is invisible to
// them — but do not cache row objects across frames expecting a snapshot.
export const computeAggregatedDataAtTime = (
  events: IServerMessage[],
  targetTime: number,
  nodeIds: string[],
  topology: ITransformedNodeMap,
): ISimulationAggregatedDataState => {
  const nodeIdsSig = nodeIds.join("|");
  const resumable =
    foldCache !== null &&
    foldCache.targetTime <= targetTime &&
    foldCache.nodeIdsSig === nodeIdsSig &&
    (foldCache.index === 0 ||
      events[foldCache.index - 1] === foldCache.lastEvent);
  if (!resumable) {
    foldCache = {
      index: 0,
      targetTime,
      lastEvent: null,
      nodeIdsSig,
      acc: newMonotoneAcc(nodeIds),
    };
  }
  const cache = foldCache!;
  const { acc } = cache;

  let i = cache.index;
  for (; i < events.length; i++) {
    const event = events[i];
    // Stop processing when we reach target time
    if (event.time_s > targetTime) {
      break;
    }
    foldEvent(acc, event);
  }
  cache.index = i;
  cache.targetTime = targetTime;
  cache.lastEvent = i > 0 ? events[i - 1] : null;

  // Resolve votes whose target RB/EB was unknown at vote-arrival time.
  acc.pendingVotes = drainPendingVotes(acc.chain, acc.pendingVotes);

  const result: ISimulationAggregatedDataState = {
    nodes: cloneNodeStats(acc.nodeStats),
    global: {
      praosTxOnChain: 0,
      leiosTxOnChain: 0,
    },
    messages: [],
    edges: new Map(),
    traversedEdges: new Set(acc.traversedEdges),
    nodeActivity: new Map(),
    eventCounts: {
      total: acc.eventCount,
      byType: { ...acc.eventCountsByType },
    },
    lastAggregatedTime: targetTime,
    chain: {
      rbs: new Map(acc.chain.rbs),
      ebs: new Map(acc.chain.ebs),
      slotZeroTime: acc.chain.slotZeroTime,
    },
  };

  buildTransitWindow(events, targetTime, topology, acc, result);

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

// Standalone chain builder for cases where we don't need to recompute the full
// aggregated state (e.g. event-batch ingestion between playback ticks).
export const buildChainAtTime = (
  events: IServerMessage[],
  targetTime: number,
): IChainState => {
  const chain: IChainState = { rbs: new Map(), ebs: new Map() };
  const pendingVotes: IVote[] = [];
  for (const event of events) {
    if (event.time_s > targetTime) break;
    const { message } = event;
    if (message.type === EServerMessageType.RBGenerated) {
      if (!chain.rbs.has(message.id)) {
        chain.rbs.set(message.id, {
          id: message.id,
          slot: message.slot,
          blockNumber: message.block_number,
          producer: message.producer,
          sizeBytes: message.size_bytes,
          parentId: message.parent?.id,
          certifiesEbId: message.endorsement?.eb.id,
          announcesEbId: message.announces?.id,
        });
        if (chain.slotZeroTime === undefined) {
          chain.slotZeroTime = event.time_s - message.slot;
        }
      }
    } else if (message.type === EServerMessageType.EBGenerated) {
      if (!chain.ebs.has(message.id)) {
        chain.ebs.set(message.id, {
          id: message.id,
          slot: message.slot,
          producer: message.producer,
          sizeBytes: message.size_bytes,
          closureSizeBytes: message.closure_size_bytes,
        });
      }
    } else if (message.type === EServerMessageType.VotesGenerated) {
      if (Array.isArray(message.votes)) {
        for (const v of message.votes) {
          const ebId = resolveVoteEbId(chain, v);
          if (ebId) creditVoteToEb(chain, v, ebId);
          else pendingVotes.push(v);
        }
      } else {
        for (const [ebId, count] of Object.entries(message.votes)) {
          const eb = chain.ebs.get(ebId);
          if (eb) eb.voteCount = (eb.voteCount ?? 0) + count;
        }
      }
    }
  }
  drainPendingVotes(chain, pendingVotes);
  return chain;
};
