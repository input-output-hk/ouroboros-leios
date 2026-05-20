import { useEffect, useRef } from "react";
import {
  forceSimulation,
  forceLink,
  forceManyBody,
  forceCenter,
  type Simulation,
  type SimulationNodeDatum,
  type SimulationLinkDatum,
} from "d3-force";
import { useStore } from "@/store";

interface ForceNode extends SimulationNodeDatum {
  nodeId: string;
}

export function useForceLayout() {
  const topology = useStore((s) => s.topology);
  const setNodePositions = useStore((s) => s.setNodePositions);
  const simRef = useRef<Simulation<ForceNode, SimulationLinkDatum<ForceNode>> | null>(null);

  useEffect(() => {
    if (!topology || topology.nodes.length === 0) return;

    if (simRef.current) {
      simRef.current.stop();
      simRef.current = null;
    }

    const nodeArray: ForceNode[] = topology.nodes.map((n, i) => ({
      nodeId: n.node_id,
      x: Math.cos((2 * Math.PI * i) / topology.nodes.length) * 200,
      y: Math.sin((2 * Math.PI * i) / topology.nodes.length) * 200,
    }));

    const idToIndex = new Map<string, number>();
    topology.nodes.forEach((n, i) => idToIndex.set(n.node_id, i));

    const linkArray: SimulationLinkDatum<ForceNode>[] = topology.edges.map(
      (e) => ({
        source: e.from,
        target: e.to,
      }),
    );

    // Scale link distance by latency (min 80, max 300)
    const maxLatency = Math.max(...topology.edges.map((e) => e.latency_ms), 1);

    const sim = forceSimulation<ForceNode>(nodeArray)
      .force(
        "link",
        forceLink<ForceNode, SimulationLinkDatum<ForceNode>>(linkArray)
          .distance((_, i) => {
            const edge = topology.edges[i];
            return edge ? 80 + (edge.latency_ms / maxLatency) * 220 : 150;
          })
          .strength(0.4),
      )
      .force("charge", forceManyBody().strength(-800))
      .force("center", forceCenter(0, 0))
      .alpha(1)
      .alphaDecay(0.05);

    // Throttle position updates: at most once per animation frame
    let dirty = false;
    let rafId: number | null = null;

    function publishPositions() {
      rafId = null;
      if (!dirty) return;
      dirty = false;
      const positions: Record<string, { x: number; y: number }> = {};
      for (const n of nodeArray) {
        positions[n.nodeId] = { x: n.x ?? 0, y: n.y ?? 0 };
      }
      setNodePositions(positions);
    }

    sim.on("tick", () => {
      dirty = true;
      if (rafId == null) {
        rafId = requestAnimationFrame(publishPositions);
      }
    });

    sim.on("end", () => {
      // Final publish to ensure we capture the settled positions
      dirty = true;
      publishPositions();
      simRef.current = null;
    });

    simRef.current = sim;

    return () => {
      sim.stop();
      if (rafId != null) cancelAnimationFrame(rafId);
    };
  }, [topology, setNodePositions]);
}
