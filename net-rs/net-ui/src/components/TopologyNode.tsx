import { memo } from "react";
import { Handle, Position, type NodeProps } from "@xyflow/react";
import { Box, Typography } from "@mui/material";
import { useStore } from "@/store";

interface TopologyNodeData {
  label: string;
  stake: number;
  selected: boolean;
}

type Props = NodeProps & { data: TopologyNodeData };

const handleStyle = {
  opacity: 0,
  top: "50%",
  left: "50%",
  transform: "translate(-50%, -50%)",
  pointerEvents: "none" as const,
};

type FlashType = "rb-produced" | "rb-received" | "eb-produced" | "eb-received" | "vote-produced" | "vote-received" | "rolledback" | null;

function borderColor(selected: boolean, flash: FlashType): string {
  if (flash === "rolledback") return "#9c27b0";
  if (flash === "rb-produced") return "#a5d6a7";
  if (flash === "rb-received") return "#81c784";
  if (flash === "eb-produced") return "#90caf9";
  if (flash === "eb-received") return "#64b5f6";
  if (flash === "vote-produced") return "#ce93d8";
  if (flash === "vote-received") return "#ba68c8";
  if (selected) return "#90caf9";
  return "#616161";
}

function bgColor(_selected: boolean, flash: FlashType): string {
  if (flash === "rolledback") return "#4a148c";
  if (flash === "rb-produced") return "#1b5e20";
  if (flash === "rb-received") return "#4e342e";
  if (flash === "eb-produced") return "#0d47a1";
  if (flash === "eb-received") return "#1a237e";
  if (flash === "vote-produced") return "#4a148c";
  if (flash === "vote-received") return "#311b92";
  return "#263238";
}

function TopologyNodeInner({ data }: Props) {
  const { label, selected } = data;
  const stats = useStore((s) => s.latestStats[label]);
  const flash = useStore((s) => s.nodeFlash[label] ?? null);
  const tip = stats?.tip_block_no;
  const tipHash = stats?.tip_hash;

  return (
    <Box
      sx={{
        width: 72,
        height: 72,
        borderRadius: "50%",
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        bgcolor: bgColor(selected, flash),
        border: selected ? 4 : 2,
        borderColor: borderColor(selected, flash),
        cursor: "pointer",
        "&:hover": { borderColor: "primary.light" },
        position: "relative",
        transition: "background-color 0.3s, border-color 0.3s",
      }}
    >
      <Typography variant="caption" fontWeight="bold" lineHeight={1.2}>
        {label}
      </Typography>
      {tip != null && (
        <Typography variant="caption" fontSize={9} color="text.secondary" lineHeight={1.2}>
          {tip}{tipHash ? ` #${tipHash}` : ""}
        </Typography>
      )}
      <Handle type="target" position={Position.Top} style={handleStyle} />
      <Handle type="source" position={Position.Bottom} style={handleStyle} />
    </Box>
  );
}

export const TopologyNode = memo(TopologyNodeInner);
