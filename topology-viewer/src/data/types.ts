export type NodeKind = "bp" | "relay";

export interface NodeFeature {
  id: string;
  lon: number;
  lat: number;
  kind: NodeKind;
  stake: number;
  provider: string | null;
  tier: string | null;
  asn: number | null;
  cc: string | null;
  region: string | null;
  ticker: string;
  pool_id: string;
  peer_count: number;
  spread_km: number;
}

export interface Corridor {
  from: string;
  to: string;
  count: number;
  mean_latency_ms: number;
  from_lon: number;
  from_lat: number;
  to_lon: number;
  to_lat: number;
}

export interface ProviderSummaryRow {
  provider: string;
  nodes: number;
  stake: number;
}

export interface TopologyMeta {
  n_nodes: number;
  n_bps: number;
  n_relays: number;
  n_edges: number;
  total_stake_ada: number;
  bidir_rate: number;
}

export interface TopologyData {
  meta: TopologyMeta;
  nodes: NodeFeature[];
  corridors_country: Corridor[];
  corridors_provider: Corridor[];
  corridors_continent: Corridor[];
  provider_summary: ProviderSummaryRow[];
}

export interface TopologyIndexEntry {
  id: string;
  label: string;
  file: string;
  n_nodes: number;
  n_edges: number;
}

export type AggregateBy = "country" | "provider" | "continent";
