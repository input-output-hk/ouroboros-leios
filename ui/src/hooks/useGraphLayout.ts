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
import { ITransformedNodeMap } from "@/components/Sim/types";

type PositionMap = Map<string, { fx: number; fy: number }>;

interface ForceNode extends SimulationNodeDatum {
  nodeId: string;
}

function originalLayout(topography: ITransformedNodeMap): PositionMap {
  const positions: PositionMap = new Map();
  for (const [id, node] of topography.nodes) {
    positions.set(id, {
      fx: node.data.location[1],
      fy: node.data.location[0],
    });
  }
  return positions;
}

function circularLayout(topography: ITransformedNodeMap): PositionMap {
  const positions: PositionMap = new Map();
  const nodeIds = Array.from(topography.nodes.keys());
  const count = nodeIds.length;
  const radius = Math.max(20, count * 1.5);

  let sumX = 0,
    sumY = 0;
  for (const [, node] of topography.nodes) {
    sumX += node.data.location[1];
    sumY += node.data.location[0];
  }
  const cx = sumX / count;
  const cy = sumY / count;

  for (let i = 0; i < count; i++) {
    const angle = (2 * Math.PI * i) / count;
    positions.set(nodeIds[i], {
      fx: cx + radius * Math.cos(angle),
      fy: cy + radius * Math.sin(angle),
    });
  }
  return positions;
}

function forceLayout(
  topography: ITransformedNodeMap,
  onTick: (positions: PositionMap) => void,
): Simulation<ForceNode, SimulationLinkDatum<ForceNode>> {
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

  const xs = nodeArray.map((n) => n.x!);
  const ys = nodeArray.map((n) => n.y!);
  const cx = (Math.min(...xs) + Math.max(...xs)) / 2;
  const cy = (Math.min(...ys) + Math.max(...ys)) / 2;

  const sim = forceSimulation<ForceNode>(nodeArray)
    .force(
      "link",
      forceLink<ForceNode, SimulationLinkDatum<ForceNode>>(linkArray)
        .distance(10)
        .strength(0.3),
    )
    .force("charge", forceManyBody().strength(-30))
    .force("center", forceCenter(cx, cy))
    .alpha(1)
    .alphaDecay(0.05);

  sim.on("tick", () => {
    const positions: PositionMap = new Map();
    for (const n of nodeArray) {
      positions.set(n.nodeId, { fx: n.x!, fy: n.y! });
    }
    onTick(positions);
  });

  return sim;
}

export const useGraphLayout = () => {
  const {
    state: { layoutMode, topography, topologyLoaded },
    dispatch,
  } = useSimContext();
  const simRef = useRef<Simulation<ForceNode, SimulationLinkDatum<ForceNode>> | null>(null);

  useEffect(() => {
    if (!topologyLoaded || topography.nodes.size === 0) return;

    if (simRef.current) {
      simRef.current.stop();
      simRef.current = null;
    }

    const applyPositions = (positions: PositionMap) =>
      dispatch({ type: "SET_NODE_POSITIONS", payload: positions });

    switch (layoutMode) {
      case "original":
        applyPositions(originalLayout(topography));
        break;
      case "circular":
        applyPositions(circularLayout(topography));
        break;
      case "auto": {
        const sim = forceLayout(topography, applyPositions);
        simRef.current = sim;
        sim.on("end", () => {
          simRef.current = null;
        });
        return () => {
          sim.stop();
        };
      }
    }
  }, [layoutMode, topologyLoaded]);
};
