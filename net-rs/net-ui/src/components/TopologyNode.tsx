import { memo } from "react";
import { Handle, Position, type NodeProps } from "@xyflow/react";
import { Box, Typography } from "@mui/material";
import type { StatsSnapshot } from "@/types";

interface TopologyNodeData {
  label: string;
  stake: number;
  stats?: StatsSnapshot;
  selected: boolean;
}

type Props = NodeProps & { data: TopologyNodeData };

function TopologyNodeInner({ data }: Props) {
  const { label, stats, selected } = data;
  const blocksProduced = stats?.blocks_produced ?? 0;

  return (
    <>
      <Handle type="target" position={Position.Top} style={{ visibility: "hidden" }} />
      <Box
        sx={{
          width: 56,
          height: 56,
          borderRadius: "50%",
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
          bgcolor: selected ? "primary.dark" : "background.paper",
          border: 2,
          borderColor: selected ? "primary.main" : "grey.700",
          cursor: "pointer",
          "&:hover": { borderColor: "primary.light" },
        }}
      >
        <Typography variant="caption" fontWeight="bold" lineHeight={1}>
          {label.replace("node-", "N")}
        </Typography>
        {stats && (
          <Typography variant="caption" fontSize={9} color="text.secondary" lineHeight={1}>
            {blocksProduced}b
          </Typography>
        )}
      </Box>
      <Handle type="source" position={Position.Bottom} style={{ visibility: "hidden" }} />
    </>
  );
}

export const TopologyNode = memo(TopologyNodeInner);
