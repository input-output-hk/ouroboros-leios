import { forceSimulation, forceLink, forceManyBody, forceCollide, type Simulation as D3Simulation } from 'd3-force';
import type { VisualEdge } from './types';

export type LayoutType = 'circular' | 'force';

export function computeCircularLayout(
  nodeIds: string[],
  width: number,
  height: number
): Map<string, { x: number; y: number }> {
  const positions = new Map<string, { x: number; y: number }>();
  const centerX = width / 2;
  const centerY = height / 2;

  // Enforce minimum node spacing
  const minArcSpacing = 20; // minimum pixels between nodes
  const defaultRadius = Math.min(width, height) * 0.4;
  const minRadiusForSpacing = (nodeIds.length * minArcSpacing) / (2 * Math.PI);
  const radius = Math.max(defaultRadius, minRadiusForSpacing);

  nodeIds.forEach((id, i) => {
    const angle = (2 * Math.PI * i) / nodeIds.length - Math.PI / 2;
    positions.set(id, {
      x: centerX + radius * Math.cos(angle),
      y: centerY + radius * Math.sin(angle),
    });
  });

  return positions;
}

export interface ForceNode {
  id: string;
  x: number;
  y: number;
  fx?: number | null;
  fy?: number | null;
}

interface ForceLink {
  source: string | ForceNode;
  target: string | ForceNode;
}

export class ForceLayoutSimulation {
  private simulation: D3Simulation<ForceNode, ForceLink>;
  private nodes: ForceNode[];
  private nodeMap: Map<string, ForceNode>;
  private onTick: (() => void) | null = null;

  constructor(nodeIds: string[], edges: VisualEdge[], width: number, height: number) {
    this.nodeMap = new Map();

    const nodeCount = nodeIds.length;
    const isLargeGraph = nodeCount > 100;

    // Scale initial radius based on node count for better spread
    const baseRadius = Math.min(width, height) * 0.35;
    const scaledRadius = isLargeGraph ? baseRadius * Math.sqrt(nodeCount / 50) : baseRadius;

    // Create nodes with initial positions spread out from center
    this.nodes = nodeIds.map((id, i) => {
      const angle = (2 * Math.PI * i) / nodeIds.length;
      const node: ForceNode = {
        id,
        x: width / 2 + scaledRadius * Math.cos(angle),
        y: height / 2 + scaledRadius * Math.sin(angle),
      };
      this.nodeMap.set(id, node);
      return node;
    });

    // Create unique links
    const seenEdges = new Set<string>();
    const links: ForceLink[] = [];
    for (const edge of edges) {
      const key = [edge.source, edge.target].sort().join('-');
      if (!seenEdges.has(key)) {
        seenEdges.add(key);
        links.push({ source: edge.source, target: edge.target });
      }
    }

    // Scale forces based on graph size for better performance and behavior
    // For large graphs, use stronger separation to spread nodes out
    // This may extend beyond viewport - user can zoom out or pan
    const linkDistance = isLargeGraph ? 60 : 80;
    const linkStrength = isLargeGraph ? 0.2 : 0.15;
    const chargeStrength = isLargeGraph ? -150 : -100;
    // Minimum distance between nodes to prevent blob clustering
    const collideRadius = isLargeGraph ? 40 : 30;

    // Create simulation - NO centering force so nodes stay where dragged
    this.simulation = forceSimulation<ForceNode, ForceLink>(this.nodes)
      .force('link', forceLink<ForceNode, ForceLink>(links)
        .id((d) => d.id)
        .distance(linkDistance)
        .strength(linkStrength))
      .force('charge', forceManyBody()
        .strength(chargeStrength)
        .distanceMax(isLargeGraph ? 150 : 300)) // Limit charge distance for performance
      .force('collide', forceCollide(collideRadius))
      .alphaDecay(0.02)
      .velocityDecay(0.3);

    this.simulation.on('tick', () => {
      if (this.onTick) this.onTick();
    });
  }

  setOnTick(callback: () => void): void {
    this.onTick = callback;
  }

  getPositions(): Map<string, { x: number; y: number }> {
    const positions = new Map<string, { x: number; y: number }>();
    for (const node of this.nodes) {
      positions.set(node.id, { x: node.x, y: node.y });
    }
    return positions;
  }

  // Start dragging a node - fix its position
  dragStart(nodeId: string, x: number, y: number): void {
    const node = this.nodeMap.get(nodeId);
    if (node) {
      node.fx = x;
      node.fy = y;
      // Reheat the simulation gently - peers will follow
      this.simulation.alphaTarget(0.1).restart();
    }
  }

  // Continue dragging - update fixed position
  drag(nodeId: string, x: number, y: number): void {
    const node = this.nodeMap.get(nodeId);
    if (node) {
      node.fx = x;
      node.fy = y;
    }
  }

  // End dragging - KEEP the node fixed where it was dropped
  // This prevents snapping back and lets users arrange the graph
  dragEnd(_nodeId: string): void {
    // Don't release the node - keep it pinned where dropped
    // The node's fx/fy remain set, so it stays in place
    // Let simulation cool down
    this.simulation.alphaTarget(0);
  }

  // Unpin a specific node (if needed in future)
  unpinNode(nodeId: string): void {
    const node = this.nodeMap.get(nodeId);
    if (node) {
      node.fx = null;
      node.fy = null;
    }
  }

  // Unpin all nodes
  unpinAll(): void {
    for (const node of this.nodes) {
      node.fx = null;
      node.fy = null;
    }
    this.simulation.alpha(0.3).restart();
  }

  // Restart simulation (e.g., after layout change)
  restart(): void {
    this.simulation.alpha(1).restart();
  }

  // Stop simulation
  stop(): void {
    this.simulation.stop();
  }
}

export function computeLayout(
  type: LayoutType,
  nodeIds: string[],
  edges: VisualEdge[],
  width: number,
  height: number
): Map<string, { x: number; y: number }> {
  if (type === 'force') {
    // For initial static computation, run simulation to completion
    const sim = new ForceLayoutSimulation(nodeIds, edges, width, height);
    // Run for a bit to get initial positions
    for (let i = 0; i < 300; i++) {
      (sim as unknown as { simulation: D3Simulation<ForceNode, ForceLink> }).simulation.tick();
    }
    const positions = sim.getPositions();
    sim.stop();
    return positions;
  }
  return computeCircularLayout(nodeIds, width, height);
}

// Controller interface for force layout with drag support
export interface ForceLayoutController {
  getPositions(): Map<string, { x: number; y: number }>;
  startDrag(nodeId: string, x: number, y: number): void;
  drag(nodeId: string, x: number, y: number): void;
  endDrag(nodeId: string): void;
  unpinNode(nodeId: string): void;
  stop(): void;
}

// Factory function to create a force layout with tick callback
export function createForceLayout(
  nodeIds: string[],
  edges: VisualEdge[],
  width: number,
  height: number,
  onTick: (positions: Map<string, { x: number; y: number }>) => void
): ForceLayoutController {
  const sim = new ForceLayoutSimulation(nodeIds, edges, width, height);

  sim.setOnTick(() => {
    onTick(sim.getPositions());
  });

  return {
    getPositions: () => sim.getPositions(),
    startDrag: (nodeId: string, x: number, y: number) => sim.dragStart(nodeId, x, y),
    drag: (nodeId: string, x: number, y: number) => sim.drag(nodeId, x, y),
    endDrag: (nodeId: string) => sim.dragEnd(nodeId),
    unpinNode: (nodeId: string) => sim.unpinNode(nodeId),
    stop: () => sim.stop(),
  };
}
