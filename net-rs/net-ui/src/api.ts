import type { Topology, StatsSnapshot, OutputEvent } from "./types";

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
