import { memo } from "react";
import {
  BaseEdge,
  EdgeLabelRenderer,
  getStraightPath,
  type EdgeProps,
} from "@xyflow/react";

interface TopologyEdgeData {
  latency_ms: number;
  selected: boolean;
}

type Props = EdgeProps & { data: TopologyEdgeData };

function TopologyEdgeInner({
  id,
  sourceX,
  sourceY,
  targetX,
  targetY,
  data,
}: Props) {
  const [edgePath, labelX, labelY] = getStraightPath({
    sourceX,
    sourceY,
    targetX,
    targetY,
  });

  const selected = data?.selected ?? false;

  return (
    <>
      <BaseEdge
        id={id}
        path={edgePath}
        style={{
          stroke: selected ? "#90caf9" : "#555",
          strokeWidth: selected ? 2 : 1,
        }}
      />
      <EdgeLabelRenderer>
        <div
          style={{
            position: "absolute",
            transform: `translate(-50%, -50%) translate(${labelX}px,${labelY}px)`,
            fontSize: 10,
            color: selected ? "#90caf9" : "#888",
            pointerEvents: "all",
            background: "#121212cc",
            padding: "0 3px",
            borderRadius: 2,
          }}
        >
          {data?.latency_ms ?? 0}ms
        </div>
      </EdgeLabelRenderer>
    </>
  );
}

export const TopologyEdge = memo(TopologyEdgeInner);
