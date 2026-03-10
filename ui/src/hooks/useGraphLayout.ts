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
import { MercatorParams } from "@/contexts/SimContext/types";

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

/** Raw Mercator: lat → y (before linear mapping) */
function rawMercatorY(lat: number): number {
  const latRad = (lat * Math.PI) / 180;
  return -Math.log(Math.tan(Math.PI / 4 + latRad / 2)) * (180 / Math.PI);
}

/** Project real-world lat/lon to the same coordinate space as the nodes */
export function mercatorProject(
  lat: number,
  lon: number,
  params: MercatorParams,
): { x: number; y: number } {
  return {
    x: params.xOffset + lon * params.xScale,
    y: params.yOffset + rawMercatorY(lat) * params.yScale,
  };
}

function mercatorLayout(
  topography: ITransformedNodeMap,
): { positions: PositionMap; params: MercatorParams } {
  // Project all nodes using raw Mercator
  const projected: { id: string; nodeLon: number; rawY: number }[] = [];
  for (const [id, node] of topography.nodes) {
    const lat = node.data.location[0];
    const lon = node.data.location[1];
    projected.push({ id, nodeLon: lon, rawY: rawMercatorY(lat) });
  }

  // Node coordinate ranges (topology space)
  const nodeLons = projected.map((p) => p.nodeLon);
  const rawYs = projected.map((p) => p.rawY);
  const nodeXMin = Math.min(...nodeLons);
  const nodeXMax = Math.max(...nodeLons);
  const rawYMin = Math.min(...rawYs);
  const rawYMax = Math.max(...rawYs);
  const nodeXSpan = nodeXMax - nodeXMin || 1;
  const rawYSpan = rawYMax - rawYMin || 1;

  // x mapping: real longitude [-180, 180] → node x range [nodeXMin, nodeXMax]
  const xScale = nodeXSpan / 360;
  const xOffset = nodeXMin - -180 * xScale;

  // y mapping: raw Mercator y → scaled y, preserving aspect ratio with x
  // Scale raw y so that the node y span matches the node x span
  const yScale = nodeXSpan / rawYSpan;
  // Center the y range on the same midpoint as x
  const nodeYMid = (nodeXMin + nodeXMax) / 2;
  const rawYMid = (rawYMin + rawYMax) / 2;
  const yOffsetCentered = nodeYMid - rawYMid * yScale;

  const params: MercatorParams = {
    xOffset,
    xScale,
    yOffset: yOffsetCentered,
    yScale,
  };

  const positions: PositionMap = new Map();
  for (const p of projected) {
    positions.set(p.id, {
      fx: p.nodeLon,
      fy: yOffsetCentered + p.rawY * yScale,
    });
  }
  return { positions, params };
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
    state: { layoutMode, topography, topologyLoaded, mapGeoJson },
    dispatch,
  } = useSimContext();
  const simRef = useRef<Simulation<ForceNode, SimulationLinkDatum<ForceNode>> | null>(null);

  // Fetch world map GeoJSON once
  useEffect(() => {
    if (mapGeoJson) return;
    fetch("data/ne_110m_admin_0_countries.geojson")
      .then((res) => {
        if (!res.ok) return null;
        return res.json();
      })
      .then((data) => {
        if (data) {
          dispatch({ type: "SET_MAP_GEOJSON", payload: data });
        }
      })
      .catch(() => {});
  }, [mapGeoJson]);

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
        dispatch({ type: "SET_MERCATOR_PARAMS", payload: null });
        applyPositions(originalLayout(topography));
        break;
      case "circular":
        dispatch({ type: "SET_MERCATOR_PARAMS", payload: null });
        applyPositions(circularLayout(topography));
        break;
      case "mercator": {
        const { positions, params } = mercatorLayout(topography);
        dispatch({ type: "SET_MERCATOR_PARAMS", payload: params });
        applyPositions(positions);
        break;
      }
      case "auto": {
        dispatch({ type: "SET_MERCATOR_PARAMS", payload: null });
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
