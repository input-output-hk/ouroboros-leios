// Mirrors Rust types from net-cluster/src/topology.rs and types.rs

export interface NodeTopology {
  index: number;
  node_id: string;
  listen_address: string;
  listen_port: number;
  stake: number;
  seed: number;
  // peers is #[serde(skip)] in Rust — use edges array instead
}

export interface Edge {
  from: number;
  to: number;
  latency_ms: number;
}

export interface Topology {
  nodes: NodeTopology[];
  edges: Edge[];
}

export interface PeerStatsEntry {
  peer_id: string;
  address: string;
  mode: string;
  rtt_ms: number | null;
  tip_block_no: number | null;
  inbound_delay_ms: number;
  bytes_sent: number;
  bytes_received: number;
}

export interface ChainTreeEntry {
  block_number: number;
  hash: string;
  prev_hash: string | null;
  tx_count: number;
  announced_eb: boolean;
  certified_eb: boolean;
  eb_tx_count: number | null;
}

export interface StatsSnapshot {
  node_id: string;
  uptime_secs: number;
  slot: number;
  tip_block_no: number | null;
  tip_hash: string | null;
  blocks_produced: number;
  blocks_received: number;
  blocks_validated: number;
  txs_generated: number;
  peer_count: number;
  peers: PeerStatsEntry[];
  chain_tree?: ChainTreeEntry[];
}

export interface OutputEvent {
  time_s: number;
  message: {
    type: string;
    node: string;
    [key: string]: unknown;
  };
}

export interface AggregatePoint {
  time: number;
  bandwidth: number;
  messages: number;
  blocks: number;
  forks: number;
}

export interface NodeSeriesPoint {
  time: number;
  bandwidth: number;
  messages: number;
  blocks: number;
}

export interface ClusterControlConfig {
  num_nodes?: number;
  degree?: number;
  min_latency_ms?: number;
  max_latency_ms?: number;
  seed?: number;
  node_config: Record<string, unknown>;
}

export type NodeVoteStatus = {
  rb_received: boolean;
  eb_received: boolean;
  vote_cast: boolean;
  perm_committee_member: boolean;
}

export interface AggregateNodeVotes {
  slot: number;
  node_statuses: Record<string, NodeVoteStatus>;
}

export interface AggregateVotesHistory {
  last_slot: number;
  node_ids: string[];
  votes: string[];
}
// Mirrors shared_consensus::leios::NoVoteReason (kebab-case serde).
export type NoVoteReason =
  | "late-eb"
  | "late-rb-header"
  | "wrong-eb"
  | "missing-tx"
  | "eb-validating"
  | "equivocating-rb"
  | "declined";

// Per-node behaviour spec — mirrors shared_consensus::behaviour::BehaviourSpec.
// The Rust enum uses #[serde(tag = "kind", rename_all = "kebab-case")].
export type BehaviourSpec =
  | { kind: "honest" }
  | { kind: "lazy-voter"; reason?: NoVoteReason }
  | { kind: "rb-header-equivocator"; ways: number }
  | { kind: "composite"; children: BehaviourSpec[] };

// Mirrors net-cluster's BehaviourSelection enum (same serde tag layout).
export type BehaviourSelection =
  | { kind: "all" }
  | { kind: "nodes"; indices: number[] }
  | { kind: "stake-random"; count: number }
  | { kind: "stake-ordered"; count: number }
  | { kind: "stake-fraction"; fraction: number };

export interface AttackRequest {
  behaviour: BehaviourSpec;
  selection: BehaviourSelection;
}

export interface ActiveAttack {
  behaviour: BehaviourSpec;
  selection: BehaviourSelection;
  indices: number[];
  started_at_s: number;
}
