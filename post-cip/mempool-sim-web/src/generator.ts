import { UndirectedGraph } from 'graphology';
import { MemoryPool } from './mempool.js';
import { Node, Link } from './types.js';

export function generateNetwork(
  n: number, 
  k: number, 
  mempool_b: number,
  latency_s: number,
  bandwidth_bps: number,
): UndirectedGraph<Node, Link> {
  
  if ((n * k) % 2 !== 0) throw new Error("n * k must be even");

  const maxAttempts = 100000;
  
  for (let attempt = 0; attempt < maxAttempts; attempt++) {
    const graph = new UndirectedGraph<Node, Link>();

    for (let i = 0; i < n; i++) {
      const nodeId = i.toString();
      graph.addNode(nodeId, {
        honest: true,
        mempool: new MemoryPool(mempool_b)
      });
    }

    let stubs: string[] = [];
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < k; j++) stubs.push(i.toString());
    }
    for (let i = stubs.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [stubs[i], stubs[j]] = [stubs[j], stubs[i]];
    }

    let success = true;
    const edgeSet = new Set<string>();

    while (stubs.length > 0) {
      const u = stubs.pop()!;
      const v = stubs.pop()!;

      if (u === v) { success = false; break; }
      const edgeKey = [u, v].sort().join("-");
      if (edgeSet.has(edgeKey)) { success = false; break; }

      edgeSet.add(edgeKey);
      
      graph.addEdge(u, v, {
        latency_s,
        bandwidth_bps,
      });
    }

    if (success) return graph;
  }

  throw new Error("Failed to generate graph");
}
