import type { Topology, StatsSnapshot, OutputEvent, ClusterControlConfig } from "./types";

const BASE = import.meta.env.VITE_API_URL ?? "";

export async function fetchTopology(): Promise<Topology> {
  const res = await fetch(`${BASE}/api/topology`);
  return res.json() as Promise<Topology>;
}

export async function fetchAllStats(): Promise<Record<string, StatsSnapshot>> {
  const res = await fetch(`${BASE}/api/stats`);
  return res.json() as Promise<Record<string, StatsSnapshot>>;
}

export async function fetchEvents(after: number): Promise<OutputEvent[]> {
  const res = await fetch(`${BASE}/api/events?after=${after}`);
  return res.json() as Promise<OutputEvent[]>;
}

export async function fetchConfig(): Promise<ClusterControlConfig> {
  const res = await fetch(`${BASE}/api/config`);
  return res.json() as Promise<ClusterControlConfig>;
}

export async function restartCluster(config: ClusterControlConfig): Promise<boolean> {
  const res = await fetch(`${BASE}/api/restart`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(config),
  });
  return res.ok;
}

export async function updateNodeConfig(nodeConfig: Record<string, unknown>): Promise<boolean> {
  const res = await fetch(`${BASE}/api/update-config`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ node_config: nodeConfig }),
  });
  return res.ok;
}
