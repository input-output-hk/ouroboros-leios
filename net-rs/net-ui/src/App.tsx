import { useEffect, useState } from "react";
import { ReactFlowProvider } from "@xyflow/react";
import { Box, IconButton, Typography } from "@mui/material";
import ChevronRightIcon from "@mui/icons-material/ChevronRight";
import ChevronLeftIcon from "@mui/icons-material/ChevronLeft";
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
  const [eventLogOpen, setEventLogOpen] = useState(true);

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
      {/* Main content */}
      <Box sx={{ flex: 1, display: "flex", flexDirection: "column", minHeight: 0, position: "relative" }}>
        {/* Header — overlay on graph */}
        <Box sx={{ position: "absolute", top: 0, left: 0, right: 0, zIndex: 20, px: 2, py: 0.75, bgcolor: "rgba(13, 27, 42, 0.6)", backdropFilter: "blur(8px)", display: "flex", alignItems: "baseline", justifyContent: "space-between", pointerEvents: "auto" }}>
          <Typography variant="h5" sx={{ color: "#ffffff", fontWeight: 700 }}>
            Leios Node Cluster
          </Typography>
          {topology && (
            <Typography variant="body2" sx={{ color: "#ffffff" }}>
              {topology.nodes.length} nodes, {topology.edges.length} edges
            </Typography>
          )}
        </Box>
        {/* Graph area — full width, all panels overlay */}
        <Box sx={{ flex: 1, minHeight: 0, position: "relative" }}>
          <ReactFlowProvider><TopologyGraph /></ReactFlowProvider>

          {/* Overlay layer — pointer-events none, children opt in */}
          <Box sx={{
            position: "absolute",
            top: 52, left: 0, right: 0, bottom: 0,
            display: "flex",
            pointerEvents: "none",
          }}>
            {/* Spacer takes remaining width */}
            <Box sx={{ flex: 1, minWidth: 0, position: "relative" }}>
              {/* Inspector + chain tree column — right-aligned within spacer */}
              <Box sx={{
                position: "absolute",
                top: 0,
                right: 0,
                bottom: 0,
                width: "40%",
                minWidth: 280,
                display: "flex",
                flexDirection: "column",
              }}>
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
                <Box sx={{ flex: 1 }} />
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

            {/* Event log toggle */}
            <Box
              onClick={() => setEventLogOpen((v) => !v)}
              sx={{
                alignSelf: "flex-start",
                mt: 1,
                pointerEvents: "auto",
                bgcolor: "rgba(40, 40, 50, 0.7)",
                backdropFilter: "blur(4px)",
                color: "#fff",
                "&:hover": { bgcolor: "rgba(60, 60, 70, 0.8)" },
                cursor: "pointer",
                display: "flex",
                alignItems: "center",
                borderRadius: 1,
                px: 0.5,
                height: 24,
              }}
            >
              {eventLogOpen
                ? <ChevronRightIcon sx={{ fontSize: 16 }} />
                : <><ChevronLeftIcon sx={{ fontSize: 16 }} /><Typography variant="caption" sx={{ fontSize: 10, mr: 0.5 }}>Events</Typography></>
              }
            </Box>

            {/* Event log */}
            <Box sx={{
              width: eventLogOpen ? 350 : 0,
              flexShrink: 0,
              transition: "width 0.2s ease",
              backdropFilter: "blur(8px)",
              bgcolor: "rgba(18, 18, 24, 0.3)",
              borderLeft: eventLogOpen ? "1px solid rgba(255,255,255,0.08)" : "none",
              display: "flex",
              flexDirection: "column",
              overflow: "hidden",
              pointerEvents: "auto",
            }}>
              {eventLogOpen && (
                <Box sx={{ flex: 1, minHeight: 0 }}>
                  <EventLog />
                </Box>
              )}
            </Box>
          </Box>
        </Box>

        {/* Charts */}
        <Box sx={{ height: 220, borderTop: 1, borderColor: "grey.800" }}>
          <AggregateCharts />
        </Box>
      </Box>
    </Box>
  );
}
