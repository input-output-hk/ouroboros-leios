import { useEffect } from "react";
import { ReactFlowProvider } from "@xyflow/react";
import { Box, Paper, Typography } from "@mui/material";
import { useStore } from "@/store";
import { usePolling } from "@/hooks/usePolling";
import { useEventStream } from "@/hooks/useEventStream";
import { useForceLayout } from "@/hooks/useForceLayout";
import { TopologyGraph } from "@/components/TopologyGraph";
import { InspectorPanel } from "@/components/InspectorPanel";
import { AggregateCharts } from "@/components/AggregateCharts";
import { ChainTreeView } from "@/components/ChainTreeView";
import { EventLog } from "@/components/EventLog";

export default function App() {
  const loadTopology = useStore((s) => s.loadTopology);
  const pollStats = useStore((s) => s.pollStats);
  const topology = useStore((s) => s.topology);
  const networkChainTree = useStore((s) => s.networkChainTree);
  const networkTipCounts = useStore((s) => s.networkTipCounts);
  const selectedNodeId = useStore((s) => s.selectedNodeId);
  const selectedEdge = useStore((s) => s.selectedEdge);

  useEffect(() => {
    loadTopology();
  }, [loadTopology]);

  useForceLayout();
  usePolling(pollStats, 1000);
  useEventStream();

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
      <Box sx={{ px: 2, py: 0.75, bgcolor: "#1a0a2e", borderBottom: 1, borderColor: "#3d1f6d", display: "flex", alignItems: "baseline", justifyContent: "space-between" }}>
        <Typography variant="h5" sx={{ color: "#ffffff", fontWeight: 700 }}>
          Leios Network
        </Typography>
        {topology && (
          <Typography variant="body2" sx={{ color: "#ffffff" }}>
            {topology.nodes.length} nodes, {topology.edges.length} edges
          </Typography>
        )}
      </Box>

      {/* Main: left (graph + charts) | right (events) */}
      <Box sx={{ flex: 1, display: "flex", minHeight: 0 }}>
        {/* Left column */}
        <Box sx={{ flex: 1, display: "flex", flexDirection: "column", minWidth: 0 }}>
          <Box sx={{ flex: 1, minHeight: 0, position: "relative" }}>
            <ReactFlowProvider><TopologyGraph /></ReactFlowProvider>
            {/* Right-side overlay column: inspector + chain tree */}
            <Box sx={{
              position: "absolute",
              top: 0,
              right: 0,
              bottom: 0,
              width: "30%",
              minWidth: 280,
              display: "flex",
              flexDirection: "column",
              pointerEvents: "none",
            }}>
              {/* Inspector — content-sized, scrolls if it would overlap chain tree */}
              {(selectedNodeId || selectedEdge) && (
                <Box sx={{
                  flex: "0 1 auto",
                  minHeight: 0,
                  overflowY: "auto",
                  backdropFilter: "blur(8px)",
                  bgcolor: "rgba(40, 40, 50, 0.5)",
                  borderLeft: "1px solid rgba(255,255,255,0.08)",
                  pointerEvents: "auto",
                }}>
                  <InspectorPanel />
                </Box>
              )}
              {/* Spacer pushes chain tree to bottom */}
              <Box sx={{ flex: 1 }} />
              {/* Network chain tree — bottom, auto-height */}
              {networkChainTree.length > 0 && (
                <Box sx={{
                  flexShrink: 0,
                  alignSelf: "flex-end",
                  borderRadius: 1,
                  px: 1,
                  py: 0.5,
                  m: 1.5,
                  pointerEvents: "auto",
                  backdropFilter: "blur(6px)",
                }}>
                  <ChainTreeView entries={networkChainTree} tipCounts={networkTipCounts} />
                </Box>
              )}
            </Box>
          </Box>
          <Box sx={{ height: 220, borderTop: 1, borderColor: "grey.800" }}>
            <AggregateCharts />
          </Box>
        </Box>

        {/* Right column — event log */}
        <Paper
          elevation={2}
          sx={{
            width: 350,
            flexShrink: 0,
            display: "flex",
            flexDirection: "column",
            borderLeft: 1,
            borderColor: "grey.800",
          }}
        >
          <Box sx={{ flex: 1, minHeight: 0 }}>
            <EventLog />
          </Box>
        </Paper>
      </Box>
    </Box>
  );
}
