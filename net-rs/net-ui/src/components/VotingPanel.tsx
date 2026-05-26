import { Box, Typography, Divider } from "@mui/material";
import { useStore } from "@/store";

type VoteCell = "NoEvent" | "RBReceived" | "EBReceived" | "VoteCast" | "Committee";

function CellIcon({ value }: { value: VoteCell }) {
  if (value === "VoteCast") {
    return (
      <Box sx={{ width: 12, height: 12, color: "#66bb6a", fontSize: 16, lineHeight: "16px", textAlign: "center", fontWeight: 700 }}>
        ✓
      </Box>
    );
  }
  if (value === "RBReceived") {
    return <Box sx={{ width: 8, height: 8, borderRadius: "50%", bgcolor: "#ef5350" }} />;
  }
  if (value === "EBReceived") {
    return <Box sx={{ width: 11, height: 11, borderRadius: "50%", bgcolor: "#fdd835" }} />;
  }
  if (value === "Committee") {
    return <Box sx={{ width: 5, height: 5, borderRadius: "50%", bgcolor: "rgba(50,50,240,0.8)" }} />;
  }
  return <Box sx={{ width: 3, height: 3, borderRadius: "50%", bgcolor: "rgba(180,180,180,0.8)" }} />;
}

export function VotingPanel() {
  const topology = useStore((s) => s.topology);
  const matrix = useStore((s) => s.votingMatrix);
  const slotStart = useStore((s) => s.votingSlotStart);

  const nodes = topology?.nodes ?? [];
  const rowCount = nodes.length;
  const colCount = matrix.length;

  return (
    <Box sx={{ p: 2, width: 700, maxWidth: "80vw" }}>
      <Typography variant="subtitle2" color="primary" gutterBottom>
        Voting Panel
      </Typography>
      <Divider sx={{ my: 1 }} />

      <Box sx={{ display: "grid", gridTemplateColumns: `160px repeat(${colCount}, 16px)`, gap: 0.5, alignItems: "center", fontSize: 11 }}>
        <Box sx={{ color: "text.secondary", fontWeight: 600 }}>Node \\ Slot</Box>
        {Array.from({ length: colCount }, (_, c) => (
          <Box key={`h-${c}`} sx={{ color: "text.secondary", textAlign: "center" }} title={`slot ${slotStart + c}`}>
            {(slotStart + c) % 1000}
          </Box>
        ))}

        {Array.from({ length: rowCount }, (_, r) => (
          <Box key={`r-${r}`} sx={{ display: "contents" }}>
            <Box sx={{ pr: 1, color: "text.primary", whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }} title={nodes[r].node_id}>
              {nodes[r].node_id}
            </Box>
            {Array.from({ length: colCount }, (_, c) => {
              const value = (matrix[c]?.[r] ?? "NoEvent") as VoteCell;
              return (
                <Box key={`c-${c}-r-${r}`} sx={{ display: "flex", alignItems: "center", justifyContent: "center", width: 16, height: 16 }}>
                  <CellIcon value={value} />
                </Box>
              );
            })}
          </Box>
        ))}
      </Box>
    </Box>
  );
}
