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
}

export interface NodeSeriesPoint {
  time: number;
  bandwidth: number;
  messages: number;
  blocks: number;
}
