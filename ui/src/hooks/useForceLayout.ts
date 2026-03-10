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
import { useSimContext } from "@/contexts/SimContext/context";

interface ForceNode extends SimulationNodeDatum {
  nodeId: string;
}

export const useForceLayout = () => {
  const {
    state: { layoutMode, topography, topologyLoaded },
    dispatch,
  } = useSimContext();
  const simRef = useRef<Simulation<ForceNode, SimulationLinkDatum<ForceNode>> | null>(null);

  useEffect(() => {
    if (!topologyLoaded || topography.nodes.size === 0) return;

    // Stop any running simulation
    if (simRef.current) {
      simRef.current.stop();
      simRef.current = null;
    }

    if (layoutMode === "original") {
      // Restore original positions from data.location
      const positions = new Map<string, { fx: number; fy: number }>();
      for (const [id, node] of topography.nodes) {
        positions.set(id, {
          fx: node.data.location[1],
          fy: node.data.location[0],
        });
      }
      dispatch({ type: "SET_NODE_POSITIONS", payload: positions });
      return;
    }

    // layoutMode === "auto": run d3-force
    const nodeArray: ForceNode[] = [];
    const idToIndex = new Map<string, number>();
    let i = 0;
    for (const [id, node] of topography.nodes) {
      nodeArray.push({ nodeId: id, x: node.fx, y: node.fy });
      idToIndex.set(id, i++);
    }

    const linkArray: SimulationLinkDatum<ForceNode>[] = [];
    for (const [, link] of topography.links) {
      const si = idToIndex.get(link.source);
      const ti = idToIndex.get(link.target);
      if (si !== undefined && ti !== undefined) {
        linkArray.push({ source: si, target: ti });
      }
    }

    // Center on bounding box midpoint of current positions
    const xs = nodeArray.map((n) => n.x!);
    const ys = nodeArray.map((n) => n.y!);
    const cx = (Math.min(...xs) + Math.max(...xs)) / 2;
    const cy = (Math.min(...ys) + Math.max(...ys)) / 2;

    const sim = forceSimulation<ForceNode>(nodeArray)
      .force(
        "link",
        forceLink<ForceNode, SimulationLinkDatum<ForceNode>>(linkArray).distance(10).strength(0.3),
      )
      .force("charge", forceManyBody().strength(-30))
      .force("center", forceCenter(cx, cy))
      .alpha(1)
      .alphaDecay(0.05);

    simRef.current = sim;

    sim.on("tick", () => {
      const positions = new Map<string, { fx: number; fy: number }>();
      for (const n of nodeArray) {
        positions.set(n.nodeId, { fx: n.x!, fy: n.y! });
      }
      dispatch({ type: "SET_NODE_POSITIONS", payload: positions });
    });

    sim.on("end", () => {
      simRef.current = null;
    });

    return () => {
      sim.stop();
    };
  }, [layoutMode, topologyLoaded]);
};
