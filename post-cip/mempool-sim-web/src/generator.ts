import { DirectedGraph } from 'graphology';
import { MemoryPool } from './mempool.js';
import type { Node, Link } from './types.js';

export function generateNetwork(
  n: number, 
  k: number, 
  mempool_B: number,
  latency_s: number,
  bandwidth_Bps: number,
): DirectedGraph<Node, Link> {
  
  if (k >= n) throw new Error("Degree k must be less than number of nodes n.");

  const makeId = (i: number): string => {
    return "H" + (i + 1);
  };

  const graph = new DirectedGraph<Node, Link>();
  for (let i = 0; i < n; i++) {
    graph.addNode(makeId(i), {
      honest: true,
      mempool: new MemoryPool(mempool_B),
    });
  }

  for (let i = 0; i < n; i++) {
    for (let offset = 1; offset <= k; offset++) {
      const target = (i + offset) % n;
      graph.addDirectedEdge(makeId(i), makeId(target), {
        latency_s,
        bandwidth_Bps,
      });
    }
  }

  const iterations = n * k * 1000; 
  const nodes = graph.nodes();

  for (let step = 0; step < iterations; step++) {
    const u = nodes[Math.floor(Math.random() * n)];
    const x = nodes[Math.floor(Math.random() * n)];

    if (u === x) continue;

    const uNeighbors = graph.outNeighbors(u);
    const xNeighbors = graph.outNeighbors(x);

    const v = uNeighbors[Math.floor(Math.random() * uNeighbors.length)];
    const y = xNeighbors[Math.floor(Math.random() * xNeighbors.length)];

    if (u === y || x === v) continue;
    
    if (graph.hasDirectedEdge(u, y) || graph.hasDirectedEdge(x, v)) continue;

    const attrsUV = graph.getDirectedEdgeAttributes(u, v);
    const attrsXY = graph.getDirectedEdgeAttributes(x, y);

    graph.dropDirectedEdge(u, v);
    graph.dropDirectedEdge(x, y);

    graph.addDirectedEdge(u, y, attrsUV);
    graph.addDirectedEdge(x, v, attrsXY);
  }

  return graph;
}


export function addAdversaryNode(
  graph: DirectedGraph<Node, Link>,
  id: string,
  upstreamCount: number,
  downstreamCount: number,
  mempool_B: number,
  latency_s: number,
  bandwidth_Bps: number,
) {
  if (graph.hasNode(id)) {
    throw new Error(`Node with ID "${id}" already exists.`);
  }

  const existingNodes = graph.nodes()

  graph.addNode(id, {
    honest: false,
    mempool: new MemoryPool(mempool_B)
  });

  if (upstreamCount > existingNodes.length || downstreamCount > existingNodes.length) {
    throw new Error("Cannot connect to more nodes than exist in the graph.");
  }

  const pickRandomNodes = (count: number): string[] => {
    const pool = [...existingNodes];
    for (let i = 0; i < count; i++) {
      const rand = i + Math.floor(Math.random() * (pool.length - i));
      [pool[i], pool[rand]] = [pool[rand], pool[i]];
    }
    return pool.slice(0, count);
  };

  const incomingSources = pickRandomNodes(upstreamCount);
  for (const source of incomingSources) {
    graph.addDirectedEdge(source, id, {
      latency_s,
      bandwidth_Bps,
    });
  }

  const outgoingTargets = pickRandomNodes(downstreamCount);
  for (const target of outgoingTargets) {
    graph.addDirectedEdge(id, target, {
      latency_s,
      bandwidth_Bps,
    });
  }
}
