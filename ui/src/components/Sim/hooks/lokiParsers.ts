// Parsing layer between cardano-node Loki log lines and the visualizer's
// internal event types. Pure functions, no DOM / no React — safe to import
// from a Web Worker. The pending-* maps below are module-level state that
// accumulates across calls within a single worker instance; the worker
// calls `resetPendingState()` on (re)connect so the maps don't survive
// stale across sessions.

import {
  EServerMessageType,
  IEndorserBlockGenerated,
  IEndorserBlockReceived,
  IEndorserBlockSent,
  IRankingBlockGenerated,
  IRankingBlockReceived,
  IRankingBlockSent,
  IServerMessage,
  ITxsReceived,
  ITxsSent,
  IVotesGenerated,
  IVotesReceived,
  IVotesSent,
} from "@/components/Sim/types";

// TODO: Replace with topology-based mapping
const HOST_PORT_TO_NODE: Record<string, string> = {
  // demo-burst with TC
  "172.28.0.110:3001": "UpstreamNode",
  "172.28.0.120:3002": "Node0",
  "172.28.0.130:3003": "DownstreamNode",
  // demo-burst without TC
  "127.1.0.1:3001": "UpstreamNode",
  "127.1.0.2:3002": "Node0",
  "127.1.0.3:3003": "DownstreamNode",
  // demo-proto-devnet with TC
  "172.28.0.10:3001": "Node1",
  "172.28.0.20:3002": "Node2",
  "172.28.0.30:3003": "Node3",
  // demo-proto-devnet without TC
  "127.2.0.1:3001": "Node1",
  "127.2.0.2:3002": "Node2",
  "127.2.0.3:3003": "Node3",
};

const getNodesFromConnection = (connectionId: string): [string, string] => {
  if (connectionId) {
    const endpoints = connectionId.split(" ");
    if (endpoints.length === 2) {
      return [HOST_PORT_TO_NODE[endpoints[0]], HOST_PORT_TO_NODE[endpoints[1]]];
    }
  }
  return ["UNKNOWN", "UNKNOWN"];
};

// Per-RB info accumulated across correlated tracer events on the producer,
// consumed when the producer adopts the block. Sized to a small cap as a
// memory bound; in practice an entry lives only ~ms before being consumed
// and deleted. Events for the same RB on the producer:
//
//   - Consensus.LeiosKernel.LeiosBlockCertified { kind: LeiosBlockCertified,
//                                                  atSlot, ebHash }
//     (only when this RB certifies an earlier EB; slot-keyed because the RB
//     hash isn't known yet)
//
//   - Consensus.LeiosKernel.LeiosBlockAnnounced { kind: LeiosBlockAnnounced,
//                                                  rbHash, ebHash, ebSlot }
//     (only when this RB announces a fresh EB; rb-hash-keyed)
//
//   - Forge.Loop.ForgedBlock { block, blockNo, blockPrev, slot }
//     promotes the slot-keyed cert (if any) to a hash-keyed entry alongside
//     parent and block-number info
//
//   - Forge.Loop.AdoptedBlock { blockHash, blockSize, slot }
//     emits the final RBGenerated, draining the hash-keyed entries
const PENDING_CAP = 256;
const pendingCerts = new Map<string, string>(); // `${producer}:${slot}` → ebHash
const pendingAnnouncements = new Map<string, string>(); // rbHash → ebHash
const pendingForges = new Map<
  string,
  { blockNo: number; blockPrev?: string; certifiesEbId?: string }
>();

export const resetPendingState = () => {
  pendingCerts.clear();
  pendingAnnouncements.clear();
  pendingForges.clear();
};

const evictOldest = <K, V>(m: Map<K, V>, cap: number) => {
  if (m.size < cap) return;
  const k = m.keys().next().value;
  if (k !== undefined) m.delete(k);
};

const parseRankingBlockGenerated = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // cardano-node tracing of newer node versions. The stream label `ns`
    // carries the tracer namespace; the `data` field is what Loki streams as
    // the log line, with the legacy `forgedBlock` wrapper flattened away.
    //
    // Two events together produce one RBGenerated, correlated by hash:
    //
    //   ns=Forge.Loop.ForgedBlock   (first)
    //   {"block":"8ee35205...","blockNo":25,"blockPrev":"625d1f62...",
    //    "kind":"TraceForgedBlock","slot":753}
    //
    //   ns=Forge.Loop.AdoptedBlock  (second, ~ms later, only on adoption)
    //   {"blockHash":"8ee35205...","blockSize":87239,
    //    "kind":"TraceAdoptedBlock","slot":753}
    //
    // ForgedBlock has parent/block_number, AdoptedBlock has size. We stash
    // the former and emit the RBGenerated message on the latter — so a
    // forged-but-not-adopted block (loser in a fork) doesn't appear in the
    // chain view, which matches "what made it into the chain".

    // Step 1: cert. The RB hash isn't known yet — stash by producer:slot.
    if (
      log.kind === "LeiosBlockCertified" &&
      log.ebHash !== undefined &&
      log.atSlot !== undefined
    ) {
      evictOldest(pendingCerts, PENDING_CAP);
      pendingCerts.set(`${streamLabels.process}:${log.atSlot}`, log.ebHash);
      return null;
    }

    // Step 1b: announcement. Direct rb-hash → eb-hash mapping; the trace
    // carries both so no slot-keyed indirection is needed.
    if (
      log.kind === "LeiosBlockAnnounced" &&
      log.rbHash !== undefined &&
      log.ebHash !== undefined
    ) {
      evictOldest(pendingAnnouncements, PENDING_CAP);
      pendingAnnouncements.set(log.rbHash, log.ebHash);
      return null;
    }

    // Step 2: forge. Promote the cert (if any) from slot-keyed to hash-keyed.
    if (streamLabels.ns === "Forge.Loop.ForgedBlock" && log.block) {
      const certKey = `${streamLabels.process}:${log.slot}`;
      const certifiesEbId = pendingCerts.get(certKey);
      pendingCerts.delete(certKey);
      evictOldest(pendingForges, PENDING_CAP);
      pendingForges.set(log.block, {
        blockNo: log.blockNo,
        blockPrev: log.blockPrev,
        certifiesEbId,
      });
      return null;
    }

    // Step 3: adopt. Emit a complete RBGenerated.
    if (streamLabels.ns === "Forge.Loop.AdoptedBlock" && log.blockHash) {
      const forged = pendingForges.get(log.blockHash);
      pendingForges.delete(log.blockHash);
      const announcedEbId = pendingAnnouncements.get(log.blockHash);
      pendingAnnouncements.delete(log.blockHash);
      const message: IRankingBlockGenerated = {
        type: EServerMessageType.RBGenerated,
        id: log.blockHash,
        slot: log.slot,
        producer: streamLabels.process,
        size_bytes: log.blockSize ?? 0,
        endorsement: forged?.certifiesEbId
          ? { eb: { id: forged.certifiesEbId } }
          : null,
        block_number: forged?.blockNo,
        parent: forged?.blockPrev ? { id: forged.blockPrev } : null,
        announces: announcedEbId ? { id: announcedEbId } : null,
      };
      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn(
      "Failed to parse Forge.Loop.{Forged,Adopted}Block log line:",
      logLine,
      error,
    );
  }

  return null;
};

const parseRankingBlockSent = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (log.kind === "BlockFetchServer" && log.peer && log.block) {
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: 0,
        id: log.block,
        sender,
        recipient,
      };

      return { time_s: timestamp, message };
    }

    if (log.direction === "Send" && log.msg && log.msg.kind === "MsgBlock") {
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: 0,
        id: log.msg.blockHash,
        sender,
        recipient,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.error("Failed to parse RankingBlockSent log line:", logLine, error);
  }

  return null;
};

const parseRankingBlockReceived = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (log.kind === "CompletedBlockFetch" && log.peer && log.block) {
      const [recipient, sender] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: IRankingBlockReceived = {
        type: EServerMessageType.RBReceived,
        slot: 0, // FIXME: use proper slot
        id: log.block,
        sender,
        recipient,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.warn(
      "Failed to parse RankingBlockReceived log line:",
      logLine,
      error,
    );
  }

  return null;
};

const parseEndorserBlockGenerated = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (log.kind === "LeiosBlockForged") {
      const message: IEndorserBlockGenerated = {
        type: EServerMessageType.EBGenerated,
        id: log.hash,
        slot: log.slot,
        producer: streamLabels.process,
        size_bytes: log.ebSize,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.warn("Failed to parse LeiosBlockForged log line:", logLine, error);
  }

  return null;
};

const parseEndorserBlockSent = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (
      (log.direction || log.kind) === "Send" &&
      log.msg &&
      log.msg.kind === "MsgLeiosBlock"
    ) {
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: IEndorserBlockSent = {
        type: EServerMessageType.EBSent,
        slot: 0, // TODO: add slot (full point) to logs?
        id: log.msg.ebHash,
        sender,
        recipient,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.error(
      "Failed to parse EndorserBlockSent log line:",
      logLine,
      error,
    );
  }

  return null;
};

const parseEndorserBlockReceived = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosBlock") {
      const [recipient, sender] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: IEndorserBlockReceived = {
        type: EServerMessageType.EBReceived,
        slot: 0, // FIXME: use correct slot
        id: log.msg.ebHash,
        sender,
        recipient,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.warn(
      "Failed to parse EndorserBlockReceived log line:",
      logLine,
      error,
    );
  }

  return null;
};

const txsId = (msg: any): string => {
  const bitmapStr = (msg.bitmaps || []).join(",");
  return `txs-${msg.ebHash}-${bitmapStr}`;
};

const parseTxsSent = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (
      (log.direction || log.kind) === "Send" &&
      log.msg &&
      log.msg.kind === "MsgLeiosBlockTxs"
    ) {
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: ITxsSent = {
        type: EServerMessageType.TxsSent,
        id: txsId(log.msg),
        sender,
        recipient,
        num_txs: log.msg.numTxs || 0,
        msg_size_bytes: log.msg.txsBytesSize,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.error("Failed to parse TxsSent log line:", logLine, error);
  }

  return null;
};

const parseTxsReceived = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosBlockTxs") {
      const [recipient, sender] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: ITxsReceived = {
        type: EServerMessageType.TxsReceived,
        id: txsId(log.msg),
        num_txs: log.msg.numTxs || 0,
        sender,
        recipient,
        msg_size_bytes: log.msg.txsBytesSize,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.warn("Failed to parse TxsReceived log line:", logLine, error);
  }

  return null;
};

const parseVotesGenerated = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // `weight` is a stake fraction in [0,1]. The network-side
    // `MsgLeiosVotes` still doesn't carry weight; only the producer's
    // `LeiosVoted` does. See aggregator for how it's summed per EB.
    if (log.kind === "LeiosVoted") {
      const weight = typeof log.weight === "number" ? log.weight : undefined;
      const message: IVotesGenerated = {
        type: EServerMessageType.VotesGenerated,
        id: `vote-${log.vote.slot}-${log.vote.voterId}-${log.vote.ebHash}`,
        slot: log.vote.slot,
        producer: streamLabels.process,
        size_bytes: 100,
        votes: [
          {
            voterId: log.vote.voterId,
            ebHash: log.vote.ebHash,
            slot: log.vote.slot,
            weight,
          },
        ],
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.warn("Failed to parse LeiosVoted log line:", logLine, error);
  }

  return null;
};

const parseVotesSent = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // Old (pre-rename): votes carried `electionId` instead of `slot`.
    if (
      (log.direction || log.kind) === "Send" &&
      log.msg &&
      log.msg.kind === "MsgLeiosVotes"
    ) {
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const votes = (log.msg.votes || []).map((v: any) => ({
        voterId: v.voterId,
        ebHash: v.ebHash,
        slot: v.slot ?? v.electionId,
      }));
      const firstVote = votes[0] || {};
      const voteId = `vote-${firstVote.slot}-${firstVote.voterId}-${firstVote.ebHash}`;

      const message: IVotesSent = {
        type: EServerMessageType.VotesSent,
        slot: firstVote.slot || 0,
        id: voteId,
        sender,
        recipient,
        votes,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.error("Failed to parse VotesSent log line:", logLine, error);
  }

  return null;
};

const parseVotesReceived = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosVotes") {
      const [recipient, sender] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const votes = (log.msg.votes || []).map((v: any) => ({
        voterId: v.voterId,
        ebHash: v.ebHash,
        slot: v.slot ?? v.electionId,
      }));
      const firstVote = votes[0] || {};
      const voteId = `vote-${firstVote.slot}-${firstVote.voterId}-${firstVote.ebHash}`;

      const message: IVotesReceived = {
        type: EServerMessageType.VotesReceived,
        slot: firstVote.slot || 0,
        id: voteId,
        sender,
        recipient,
        votes,
      };

      return { time_s: timestamp, message };
    }
  } catch (error) {
    console.warn("Failed to parse VotesReceived log line:", logLine, error);
  }

  return null;
};

// Chain the per-kind parsers in the original order. The first one to claim
// the line wins; all others see the line but should return null for kinds
// they don't recognize.
export const parseStreamValue = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null =>
  parseRankingBlockGenerated(streamLabels, timestamp, logLine) ||
  parseRankingBlockSent(timestamp, logLine) ||
  parseRankingBlockReceived(timestamp, logLine) ||
  parseEndorserBlockGenerated(streamLabels, timestamp, logLine) ||
  parseEndorserBlockSent(timestamp, logLine) ||
  parseEndorserBlockReceived(timestamp, logLine) ||
  parseTxsSent(timestamp, logLine) ||
  parseTxsReceived(timestamp, logLine) ||
  parseVotesGenerated(streamLabels, timestamp, logLine) ||
  parseVotesSent(timestamp, logLine) ||
  parseVotesReceived(timestamp, logLine);
