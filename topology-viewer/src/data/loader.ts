import type { TopologyData, TopologyIndexEntry } from "./types";

const CACHE = new Map<string, TopologyData>();

export async function loadIndex(): Promise<TopologyIndexEntry[]> {
  const r = await fetch("./data/index.json");
  if (!r.ok) throw new Error(`Failed to load index.json: ${r.status}`);
  const j = await r.json();
  return j.topologies as TopologyIndexEntry[];
}

export async function loadTopology(id: string): Promise<TopologyData> {
  if (CACHE.has(id)) return CACHE.get(id)!;
  const r = await fetch(`./data/${id}.json`);
  if (!r.ok) throw new Error(`Failed to load ${id}: ${r.status}`);
  const data = (await r.json()) as TopologyData;
  CACHE.set(id, data);
  return data;
}
