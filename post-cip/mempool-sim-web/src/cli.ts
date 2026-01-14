import { generateNetwork, addAdversaryNode } from './generator.js';

const NODES = 50;
const DEGREE = 6;
const BLOCK = 90000;
const MEMPOOL = 2 * BLOCK;
const LATENCY = 0.100; // = 100 ms
const BANDWIDTH = 1250000; // = 10 Mb/s

const ADVERSARY_COUNT = 2;
const ADVERSARY_DEGREE = 3 * DEGREE;

try {
  console.log(`Generating a ${DEGREE}-regular graph with ${NODES} nodes...`);
  const graph = generateNetwork(NODES, DEGREE, MEMPOOL, LATENCY, BANDWIDTH);

  console.log("✅ Success!");
  console.log(`Nodes: ${graph.order}, Edges: ${graph.size}`);
  
  for (let i = 0; i < ADVERSARY_COUNT; ++i) {
    addAdversaryNode(graph, "A" + (i + 1), 3 * DEGREE, 3 * DEGREE, MEMPOOL, LATENCY, BANDWIDTH);
  }

  console.log("\nAdjacency List:");
  graph.forEachNode((node) => {
    const neighbors = graph.outboundNeighbors(node);
    console.log(`Node ${node}: connected to [${neighbors.join(', ')}]`);
  });

} catch (error) {
  console.error("❌ Error:", error);
}
