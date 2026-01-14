import { generateRandomRegularGraph } from './generator.js';

const NODES = 50;
const DEGREE = 6;

try {
  console.log(`Generating a ${DEGREE}-regular graph with ${NODES} nodes...`);
  const graph = generateRandomRegularGraph(NODES, DEGREE);

  console.log("✅ Success!");
  console.log(`Nodes: ${graph.order}, Edges: ${graph.size}`);
  
  console.log("\nAdjacency List:");
  graph.forEachNode((node) => {
    const neighbors = graph.neighbors(node);
    console.log(`Node ${node}: connected to [${neighbors.join(', ')}]`);
  });

} catch (error) {
  console.error("❌ Error:", error);
}
