import { generateNetwork } from './generator.js';

const NODES = 50;
const DEGREE = 6;
const BLOCK_B = 90000;
const MEMPOOL_B = 2 * BLOCK_B;
const LATENCY = 0.100; // = 100 ms
const BANDWIDTH = 125000; // = 10 Mb/s

try {
  console.log(`Generating a ${DEGREE}-regular graph with ${NODES} nodes...`);
  const graph = generateNetwork(NODES, DEGREE, MEMPOOL_B, LATENCY, BANDWIDTH);

  console.log("✅ Success!");
  console.log(`Nodes: ${graph.order}, Edges: ${graph.size}`);
  
  console.log("\nAdjacency List:");
  graph.forEachNode((node) => {
    const neighbors = graph.outboundNeighbors(node);
    console.log(`Node ${node}: connected to [${neighbors.join(', ')}]`);
  });

} catch (error) {
  console.error("❌ Error:", error);
}
