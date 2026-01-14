import { DirectedGraph } from 'graphology';
import { MemoryPool } from './mempool.js';
import { Node, Link } from './types.js';

export function generateNetwork(
  n: number, 
  k: number, 
  mempool_B: number,
  latency_s: number,
  bandwidth_Bps: number,
): DirectedGraph<Node, Link> {
  
  if (k >= n) throw new Error("Degree k must be less than number of nodes n.");

  const graph = new DirectedGraph<Node, Link>();
  for (let i = 0; i < n; i++) {
    graph.addNode(i.toString(), {
      honest: true,
      mempool: new MemoryPool(mempool_B),
    });
  }

  for (let i = 0; i < n; i++) {
    for (let offset = 1; offset <= k; offset++) {
      const target = (i + offset) % n;
      graph.addDirectedEdge(i.toString(), target.toString(), {
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
