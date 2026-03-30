import { useEffect } from "react";
import { ReactFlowProvider } from "@xyflow/react";
import { Box, Paper, Typography } from "@mui/material";
import { useStore } from "@/store";
import { usePolling } from "@/hooks/usePolling";
import { useForceLayout } from "@/hooks/useForceLayout";
import { TopologyGraph } from "@/components/TopologyGraph";
import { InspectorPanel } from "@/components/InspectorPanel";
import { AggregateCharts } from "@/components/AggregateCharts";
import { EventLog } from "@/components/EventLog";

export default function App() {
  const loadTopology = useStore((s) => s.loadTopology);
  const pollStats = useStore((s) => s.pollStats);
  const pollEvents = useStore((s) => s.pollEvents);
  const topology = useStore((s) => s.topology);

  useEffect(() => {
    loadTopology();
  }, [loadTopology]);

  useForceLayout();
  usePolling(pollStats, 1000);
  usePolling(pollEvents, 1000);

  return (
    <Box
      sx={{
        height: "100vh",
        display: "flex",
        flexDirection: "column",
        bgcolor: "background.default",
        overflow: "hidden",
      }}
    >
      {/* Header */}
      <Box sx={{ px: 2, py: 0.5, borderBottom: 1, borderColor: "divider" }}>
        <Typography variant="subtitle2" color="text.secondary">
          net-cluster dashboard
          {topology && ` — ${topology.nodes.length} nodes, ${topology.edges.length} edges`}
        </Typography>
      </Box>

      {/* Top: Graph + Inspector */}
      <Box sx={{ flex: 1, display: "flex", minHeight: 0 }}>
        <Box sx={{ flex: 1, minWidth: 0 }}>
          <ReactFlowProvider>
            <TopologyGraph />
          </ReactFlowProvider>
        </Box>
        <Paper
          elevation={2}
          sx={{
            width: 350,
            borderLeft: 1,
            borderColor: "divider",
            overflowY: "auto",
          }}
        >
          <InspectorPanel />
        </Paper>
      </Box>

      {/* Bottom: Charts + Events */}
      <Box
        sx={{
          height: 220,
          display: "flex",
          borderTop: 1,
          borderColor: "divider",
        }}
      >
        <Box sx={{ flex: 2, minWidth: 0 }}>
          <AggregateCharts />
        </Box>
        <Paper
          elevation={2}
          sx={{
            flex: 1,
            minWidth: 0,
            borderLeft: 1,
            borderColor: "divider",
          }}
        >
          <EventLog />
        </Paper>
      </Box>
    </Box>
  );
}
