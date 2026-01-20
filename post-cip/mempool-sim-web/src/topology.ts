import { DirectedGraph } from 'graphology';
import { Node } from './node.js';
import { Link } from './link.js'
import { logger } from './logger.js';

export function generateNetwork(
  n: number, 
  k: number, 
  mempool_B: number,
  latency_s: number,
  bandwidth_Bps: number,
): DirectedGraph<Node, Link> {
  
  if (k >= n) {
    logger.fatal({nodes: n, degree: k}, "degree must be less than number of nodes");
    throw new Error("degree must be less than number of nodes");
  }

  const makeId = (i: number): string => {
    return "H" + (i + 1);
  };

  const graph = new DirectedGraph<Node, Link>();
  for (let i = 0; i < n; i++) {
    const id: string = makeId(i);
    graph.addNode(id, new Node(id, true, NaN, mempool_B));
  }

  for (let i = 0; i < n; i++) {
    for (let offset = 1; offset <= k; offset++) {
      const target = (i + offset) % n;
      graph.addDirectedEdge(makeId(i), makeId(target), new Link(latency_s,
        bandwidth_Bps,
      ));
    }
  }

  const iterations = n * k * 100; 
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
  frontrunDelay: number,
  mempool_B: number,
  latency_s: number,
  bandwidth_Bps: number,
) {
  if (graph.hasNode(id)) {
    logger.fatal({node: id}, "node with ID already exists");
    throw new Error(`node with ID already exists`);
  }

  const existingNodes = graph.nodes()

  graph.addNode(id, new Node(id, false, frontrunDelay, mempool_B));

  if (upstreamCount > existingNodes.length || downstreamCount > existingNodes.length) {
    logger.fatal("cannot connect to more nodes than exist in the graph.")
    throw new Error("cannot connect to more nodes than exist in the graph");
  }

  const pickRandomNodes = (count: number): string[] => {
    const pool = [...existingNodes];
    for (let i = 0; i < count; i++) {
      const j = i + Math.floor(Math.random() * (pool.length - i));
      [pool[i], pool[j]] = [pool[j]!, pool[i]!];
    }
    return pool.slice(0, count);
  };

  const incomingSources = pickRandomNodes(upstreamCount);
  for (const source of incomingSources) {
    graph.addDirectedEdge(
      source, 
      id, 
      new Link(latency_s, bandwidth_Bps),
    );
  }

  const outgoingTargets = pickRandomNodes(downstreamCount);
  for (const target of outgoingTargets) {
    graph.addDirectedEdge(
      id, 
      target, 
      new Link(latency_s, bandwidth_Bps),
    );
  }
}
