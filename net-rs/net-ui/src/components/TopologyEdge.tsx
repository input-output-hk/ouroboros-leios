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
  flash?: "connected" | "disconnected" | null;
  status?: "connected" | "disconnected" | null;
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
  const flash = data?.flash ?? null;
  const status = data?.status ?? null;

  // Flash takes priority (event animation), then selection, then
  // steady-state status, then default.  Connected edges render
  // light green; disconnected edges render pink; unknown (no
  // events yet) stays gray.  Width is bumped only during flashes.
  const stroke =
    flash === "connected"
      ? "#4caf50"
      : flash === "disconnected"
        ? "#e53935"
        : selected
          ? "#90caf9"
          : status === "disconnected"
            ? "#f48fb1"
            : status === "connected"
              ? "#a5d6a7"
              : "#555";
  const strokeWidth = flash ? 3 : selected ? 2 : 1;

  return (
    <>
      <BaseEdge
        id={id}
        path={edgePath}
        style={{
          stroke,
          strokeWidth,
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
