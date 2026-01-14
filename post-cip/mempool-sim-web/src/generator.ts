import { UndirectedGraph } from 'graphology';

export function generateRandomRegularGraph(n: number, k: number, maxAttempts = 100000): UndirectedGraph {
  // validation
  if ((n * k) % 2 !== 0) throw new Error("The product of n and k must be even.");
  if (k >= n) throw new Error("Degree k must be less than number of nodes n.");

  for (let attempt = 0; attempt < maxAttempts; attempt++) {
    const graph = new UndirectedGraph();
    
    // Add nodes
    for (let i = 0; i < n; i++) graph.addNode(i.toString());

    // Create stubs
    let stubs: string[] = [];
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < k; j++) stubs.push(i.toString());
    }

    // Shuffle stubs
    for (let i = stubs.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [stubs[i], stubs[j]] = [stubs[j], stubs[i]];
    }

    // Pair stubs
    let success = true;
    const edgeSet = new Set<string>();

    while (stubs.length > 0) {
      const u = stubs.pop()!;
      const v = stubs.pop()!;

      if (u === v) { success = false; break; } // Self-loop

      const edgeKey = [u, v].sort().join("-");
      if (edgeSet.has(edgeKey)) { success = false; break; } // Multi-edge

      edgeSet.add(edgeKey);
      graph.addEdge(u, v);
    }

    if (success) return graph;
  }

  throw new Error(`Failed to generate graph after ${maxAttempts} attempts.`);
}
