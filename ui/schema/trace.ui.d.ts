/**
 * Trace event schema as consumed by the visualizer UI.
 *
 * The UI ingests two trace sources:
 *  - Offline simulator JSONL traces (sim-rs, leios-sim).
 *  - Live Loki streams from `cardano-node` running the Leios consensus
 *    prototype — parsed in `ui/src/components/Sim/hooks/useLokiWebSocket.ts`.
 *
 * This schema is self-contained: it does not reuse simulator types and
 * intentionally reflects only the subset of fields the UI cares about.
 * Where the same conceptual event has both a simulator name and a
 * prototype name (e.g. `VTBundleSent` / `VotesSent`), one record covers
 * both via a `type` literal union. Each event is a flat record listing
 * exactly its own fields, with optionality reflecting cross-source
 * reality. Drift against actual stored traces is caught in CI by
 * `npm run validate:traces`.
 */

// --- Shared sub-records --------------------------------------------------

/** A single vote as carried in the prototype's `MsgLeiosVotes` payloads. */
export interface Vote {
  voterId: number;
  /** Hash of the announcing RB the vote targets. Current prototype shape:
   *  votes are cast on the RB that announced the EB, not on the EB itself. */
  rbHash?: string;
  /** EB hash, carried by simulator traces and by older prototype traces
   *  (pre-"vote on the announcing RbHash" change). */
  ebHash?: string;
  /** Slot of the EB being voted on (older prototype trace format). */
  slot?: number;
  /** Legacy field name for `slot`, kept for very old prototype traces. */
  electionId?: number;
  voteSignature?: boolean;
  /** Stake-weighted vote weight, as a fraction of total stake in [0,1].
   *  Currently only carried by the producer's `LeiosVoted` trace; the
   *  network-side `MsgLeiosVotes` doesn't surface weights yet. */
  weight?: number;
}

/** Reference to a block by its identifier. */
export interface BlockRef {
  id: string;
}

/** Endorsement carried in a ranking block. */
export interface Endorsement {
  eb: BlockRef;
}

// --- Generated events -----------------------------------------------------

/** Transaction-generation event. `TXGenerated` is the simulator name;
 *  `TxsGenerated` is the post-normalisation name used inside the UI. */
export interface UITxsGenerated {
  type: "TxsGenerated" | "TXGenerated";
  id: string;
  publisher: string;
  size_bytes: number;
}

export interface UIRBGenerated {
  type: "RBGenerated";
  id: string;
  slot: number;
  producer: string;
  size_bytes: number;
  endorsement: Endorsement | null;
  endorsements?: Endorsement[] | null;
  /** Carried by the simulator; omitted by the prototype. */
  parent?: BlockRef | null;
  /** Carried by the simulator; omitted by the prototype. */
  tx_payload_bytes?: number;
  /** Sequential block height on the RB chain. Not yet emitted by either source. */
  block_number?: number;
  /** EB announced by this RB's header. Header-level relation, distinct from
   *  `endorsement` (which is the body-level certification). Not yet emitted
   *  by either source. */
  announces?: BlockRef | null;
}

export interface UIEBGenerated {
  type: "EBGenerated";
  id: string;
  slot: number;
  producer: string;
  size_bytes: number;
}

/** Vote-generation event. `VTBundleGenerated` is the simulator name;
 *  `VotesGenerated` is what the prototype emits. The `votes` payload also
 *  differs in shape: simulator emits a weight map keyed by voter id, the
 *  prototype emits an array of per-vote records. */
export interface UIVotesGenerated {
  type: "VotesGenerated" | "VTBundleGenerated";
  id: string;
  slot: number;
  producer: string;
  size_bytes: number;
  votes: { [voterId: string]: number } | Vote[];
}

// --- Network: Sent --------------------------------------------------------

export interface UIRBSent {
  type: "RBSent";
  id: string;
  sender: string;
  recipient: string;
  /** Carried by the simulator; omitted by the prototype. */
  msg_size_bytes?: number;
  sending_s?: number;
  slot: number;
  ids?: string[];
}

export interface UIEBSent {
  type: "EBSent";
  id: string;
  sender: string;
  recipient: string;
  /** Carried by the simulator; omitted by the prototype. */
  msg_size_bytes?: number;
  sending_s?: number;
  slot: number;
  ids?: string[];
}

/** Sent event for a vote-bundle message. `VTBundleSent` is the simulator
 *  name; `VotesSent` is what the prototype emits. */
export interface UIVotesSent {
  type: "VotesSent" | "VTBundleSent";
  id: string;
  sender: string;
  recipient: string;
  /** Carried by the simulator; omitted by the prototype. */
  msg_size_bytes?: number;
  sending_s?: number;
  slot: number;
  ids?: string[];
  /** Per-vote records as emitted by the prototype; the simulator omits this. */
  votes?: Vote[];
}

/** Sent event for transactions. `TXSent` is the simulator name; `TxsSent`
 *  is what the prototype emits. */
export interface UITxsSent {
  type: "TxsSent" | "TXSent";
  id: string;
  sender: string;
  recipient: string;
  msg_size_bytes: number;
  sending_s?: number;
  slot?: number;
  ids?: string[];
  /** Number of transactions in the message — prototype only. */
  num_txs?: number;
}

// --- Network: Received ----------------------------------------------------

export interface UIRBReceived {
  type: "RBReceived";
  id: string;
  recipient: string;
  sender?: string;
  slot: number;
  ids?: string[];
}

export interface UIEBReceived {
  type: "EBReceived";
  id: string;
  recipient: string;
  sender?: string;
  slot: number;
  ids?: string[];
}

/** Received event for a vote-bundle message. `VTBundleReceived` is the
 *  simulator name; `VotesReceived` is what the prototype emits. */
export interface UIVotesReceived {
  type: "VotesReceived" | "VTBundleReceived";
  id: string;
  recipient: string;
  sender?: string;
  slot: number;
  ids?: string[];
  /** Per-vote records as emitted by the prototype; the simulator omits this. */
  votes?: Vote[];
}

/** Received event for transactions. `TXReceived` is the simulator name;
 *  `TxsReceived` is what the prototype emits. */
export interface UITxsReceived {
  type: "TxsReceived" | "TXReceived";
  id: string;
  recipient: string;
  sender?: string;
  slot?: number;
  ids?: string[];
  /** Carried by the prototype; the simulator omits this. */
  msg_size_bytes?: number;
  /** Number of transactions in the message — prototype only. */
  num_txs?: number;
}

// --- Union ----------------------------------------------------------------

/** Union of every message shape the UI renders. */
export type UIMessage =
  | UITxsGenerated
  | UIRBGenerated
  | UIEBGenerated
  | UIVotesGenerated
  | UIRBSent
  | UIEBSent
  | UIVotesSent
  | UITxsSent
  | UIRBReceived
  | UIEBReceived
  | UIVotesReceived
  | UITxsReceived;

/** Set of `message.type` strings the UI renders — also used by CI to filter
 *  a trace before validating it against this schema. */
export type UIMessageType = UIMessage["type"];

/** Top-level event entry as produced by either trace source. */
export interface UITraceEvent {
  time_s: number;
  message: UIMessage;
}

/** A whole trace file represented as an array (e.g. after `jq -cs '.'`). */
export type UITraceEvents = UITraceEvent[];
