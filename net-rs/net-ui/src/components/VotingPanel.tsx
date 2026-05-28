import { Box, Typography, Divider } from "@mui/material";
import { useStore } from "@/store";

type VoteCell = "NoEvent" | "RBReceived" | "EBReceived" | "EBGenerated" | "VoteCast" | "Committee" | "Incorrect";

function CellIcon({ value }: { value: VoteCell }) {
  if (value === "VoteCast") {
    return (
      <Box sx={{ width: 12, height: 12, color: "#66bb6a", fontSize: 16, lineHeight: "16px", textAlign: "center", fontWeight: 700 }}>
        ✓
      </Box>
    );
  }
  if (value === "EBGenerated") {
    return (
      <Box sx={{ width: 14, height: 14, borderRadius: "50%", border: "1px solid #66bb6a", display: "flex", alignItems: "center", justifyContent: "center" }}>
        <Box sx={{ color: "#66bb6a", fontSize: 11, lineHeight: "11px", fontWeight: 700 }}>✓</Box>
      </Box>
    );
  }
  if (value === "RBReceived") {
    return <Box sx={{ width: 6, height: 6, borderRadius: "50%", bgcolor: "#fdd835" }} />;
  }
  if (value === "EBReceived") {
    return <Box sx={{ width: 11, height: 11, borderRadius: "50%", bgcolor: "#00eeee" }} />;
  }
  if (value === "Committee") {
    return <Box sx={{ width: 5, height: 5, borderRadius: "50%", bgcolor: "rgba(50,50,240,0.8)" }} />;
  }
  if (value === "Incorrect") {
    return <Box sx={{ width: 8, height: 8, borderRadius: "50%", bgcolor: "#ff1010" }} />;
  }
  return <Box sx={{ width: 2, height: 2, borderRadius: "50%", bgcolor: "rgba(180,180,180,0.8)" }} />;
}

export function VotingPanel() {
  const topology = useStore((s) => s.topology);
  const matrix = useStore((s) => s.votingMatrix);
  const slotStart = useStore((s) => s.votingSlotStart);

  const nodes = topology?.nodes ?? [];
  const rowCount = nodes.length;
  const colCount = matrix.length;

  return (
    <Box sx={{ p: 2, width: 820, maxWidth: "90vw", display: "flex", gap: 3 }}>
      <Box sx={{ flex: 1 }}>
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

      {/* Legend */}
      <Box sx={{ minWidth: 120, pt: 4, display: "flex", flexDirection: "column", gap: 1 }}>
        <Typography variant="caption" color="text.secondary" sx={{ fontWeight: 600, mb: 0.5 }}>Legend</Typography>
        <LegendItem value="VoteCast" label="Vote cast, EB+RB received" />
        <LegendItem value="EBGenerated" label="Vote cast, EB generated" />
        <LegendItem value="EBReceived" label="EB+RB received" />
        <LegendItem value="RBReceived" label="RB received" />
        <LegendItem value="Committee" label="Committee member" />
        <LegendItem value="Incorrect" label="Other combination" />
        <LegendItem value="NoEvent" label="No event" />
      </Box>
    </Box>
  );
}

function LegendItem({ value, label }: { value: VoteCell; label: string }) {
  return (
    <Box sx={{ display: "flex", alignItems: "center", gap: 1 }}>
      <Box sx={{ width: 16, height: 16, display: "flex", alignItems: "center", justifyContent: "center" }}>
        <CellIcon value={value} />
      </Box>
      <Typography variant="caption" color="text.secondary">{label}</Typography>
    </Box>
  );
}
