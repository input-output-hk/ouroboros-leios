import { LightNode } from './node.js';
import { Link } from './link.js';
import { logger } from './logger.js';

export interface TopologyResult {
  nodes: LightNode[];
  links: Map<string, Link>;  // key: `${fromIdx}-${toIdx}`
}

function linkKey(from: number, to: number): string {
  return `${from}-${to}`;
}

/**
 * Generate a random regular directed graph of honest nodes using edge-swap randomisation.
 */
export function generateNetwork(
  n: number,
  k: number,
  mempool_B: number,
  latency_s: number,
  bandwidth_Bps: number,
): TopologyResult {
  if (k >= n) {
    throw new Error('degree must be less than number of nodes');
  }

  const nodes: LightNode[] = [];
  for (let i = 0; i < n; i++) {
    nodes.push(new LightNode(i, `H${i + 1}`, true, NaN, mempool_B));
  }

  const links = new Map<string, Link>();

  // adjacency sets for quick lookup during rewiring
  const outAdj: Set<number>[] = Array.from({ length: n }, () => new Set<number>());

  // Initial ring lattice
  for (let i = 0; i < n; i++) {
    for (let offset = 1; offset <= k; offset++) {
      const j = (i + offset) % n;
      outAdj[i]!.add(j);
      links.set(linkKey(i, j), new Link(latency_s, bandwidth_Bps));
    }
  }

  // Edge-swap randomisation
  const iterations = n * k * 100;
  for (let step = 0; step < iterations; step++) {
    const u = Math.floor(Math.random() * n);
    const x = Math.floor(Math.random() * n);
    if (u === x) continue;

    const uOut = Array.from(outAdj[u]!);
    const xOut = Array.from(outAdj[x]!);
    if (uOut.length === 0 || xOut.length === 0) continue;

    const v = uOut[Math.floor(Math.random() * uOut.length)]!;
    const y = xOut[Math.floor(Math.random() * xOut.length)]!;

    if (u === y || x === v) continue;
    if (outAdj[u]!.has(y) || outAdj[x]!.has(v)) continue;

    // Swap edges: u→v, x→y  =>  u→y, x→v
    outAdj[u]!.delete(v);
    outAdj[x]!.delete(y);
    outAdj[u]!.add(y);
    outAdj[x]!.add(v);

    const linkUV = links.get(linkKey(u, v))!;
    const linkXY = links.get(linkKey(x, y))!;
    links.delete(linkKey(u, v));
    links.delete(linkKey(x, y));
    links.set(linkKey(u, y), linkUV);
    links.set(linkKey(x, v), linkXY);
  }

  // Build peer lists on nodes
  for (let i = 0; i < n; i++) {
    nodes[i]!.downstreamPeers = Array.from(outAdj[i]!);
    // upstream = who points to me
  }
  for (let i = 0; i < n; i++) {
    for (const j of outAdj[i]!) {
      nodes[j]!.upstreamPeers.push(i);
    }
  }

  return { nodes, links };
}

/**
 * Add an adversary node to the topology, rewiring edges to insert it.
 */
export function addAdversaryNode(
  nodes: LightNode[],
  links: Map<string, Link>,
  upstreamCount: number,
  downstreamCount: number,
  frontrunDelay_s: number,
  mempool_B: number,
  latency_s: number,
  bandwidth_Bps: number,
): LightNode {
  const idx = nodes.length;
  const id = `A${idx - nodes.filter(n => !n.honest).length + 1}`;
  // count existing adversaries for naming
  let advCount = 0;
  for (const nd of nodes) if (!nd.honest) advCount++;
  const advNode = new LightNode(idx, `A${advCount + 1}`, false, frontrunDelay_s, mempool_B);
  nodes.push(advNode);

  const honestIndices = nodes.filter(n => n.honest).map(n => n.idx);

  const pickRandom = (arr: number[], count: number): number[] => {
    const pool = [...arr];
    const result: number[] = [];
    for (let i = 0; i < count && pool.length > 0; i++) {
      const j = Math.floor(Math.random() * pool.length);
      result.push(pool[j]!);
      pool[j] = pool[pool.length - 1]!;
      pool.pop();
    }
    return result;
  };

  // Upstream: rewire existing edges to point to adversary
  const incomingSources = pickRandom(honestIndices, Math.min(upstreamCount, honestIndices.length));
  for (const src of incomingSources) {
    const srcNode = nodes[src]!;
    const eligible = srcNode.downstreamPeers.filter(t => t !== idx);
    if (eligible.length > 0) {
      const oldTarget = eligible[Math.floor(Math.random() * eligible.length)]!;
      // Remove old edge
      srcNode.downstreamPeers = srcNode.downstreamPeers.filter(t => t !== oldTarget);
      nodes[oldTarget]!.upstreamPeers = nodes[oldTarget]!.upstreamPeers.filter(t => t !== src);
      links.delete(linkKey(src, oldTarget));
      // Add new edge to adversary
      srcNode.downstreamPeers.push(idx);
      advNode.upstreamPeers.push(src);
      links.set(linkKey(src, idx), new Link(latency_s, bandwidth_Bps));
    }
  }

  // Downstream: add edges from adversary to honest nodes
  const outgoingTargets = pickRandom(honestIndices, Math.min(downstreamCount, honestIndices.length));
  for (const tgt of outgoingTargets) {
    if (!links.has(linkKey(idx, tgt))) {
      advNode.downstreamPeers.push(tgt);
      nodes[tgt]!.upstreamPeers.push(idx);
      links.set(linkKey(idx, tgt), new Link(latency_s, bandwidth_Bps));
    }
  }

  return advNode;
}
