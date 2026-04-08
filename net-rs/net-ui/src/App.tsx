import { useEffect, useRef, useState } from "react";
import { ReactFlowProvider } from "@xyflow/react";
import { Box, Typography } from "@mui/material";
import { useStore } from "@/store";
import { usePolling } from "@/hooks/usePolling";
import { useEventStream } from "@/hooks/useEventStream";
import { useForceLayout } from "@/hooks/useForceLayout";
import { TopologyGraph } from "@/components/TopologyGraph";
import { InspectorPanel } from "@/components/InspectorPanel";
import { AggregateCharts } from "@/components/AggregateCharts";
import { ChainTreeView } from "@/components/ChainTreeView";
import { EventLog } from "@/components/EventLog";
import { IconSidebar } from "@/components/IconSidebar";
import { ControlPanel } from "@/components/ControlPanel";

export default function App() {
  const loadTopology = useStore((s) => s.loadTopology);
  const loadConfig = useStore((s) => s.loadConfig);
  const pollStats = useStore((s) => s.pollStats);
  const topology = useStore((s) => s.topology);
  const restarting = useStore((s) => s.restarting);
  const networkChainTree = useStore((s) => s.networkChainTree);
  const networkTipCounts = useStore((s) => s.networkTipCounts);
  const selectedNodeId = useStore((s) => s.selectedNodeId);
  const selectedEdge = useStore((s) => s.selectedEdge);
  const [eventLogOpen, setEventLogOpen] = useState(true);
  const [chartsOpen, setChartsOpen] = useState(true);
  const [chainTreeOpen, setChainTreeOpen] = useState(true);
  const [controlPanelOpen, setControlPanelOpen] = useState(false);

  useEffect(() => {
    loadTopology();
    loadConfig();
  }, [loadTopology, loadConfig]);

  // Close control panel when restart completes.
  const wasRestarting = useRef(false);
  useEffect(() => {
    if (wasRestarting.current && !restarting) {
      setControlPanelOpen(false);
    }
    wasRestarting.current = restarting;
  }, [restarting]);

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
      {/* Graph fills entire area */}
      <Box sx={{ flex: 1, minHeight: 0, position: "relative" }}>
        <ReactFlowProvider><TopologyGraph /></ReactFlowProvider>

        {/* Icon sidebar — absolute, left side, below header */}
        <Box sx={{ position: "absolute", top: 42, left: 0, bottom: 0, zIndex: 25, pointerEvents: "auto" }}>
          <IconSidebar
            controlPanelOpen={controlPanelOpen}
            onToggleControlPanel={() => setControlPanelOpen((v) => !v)}
            chainTreeOpen={chainTreeOpen}
            onToggleChainTree={() => setChainTreeOpen((v) => !v)}
            chartsOpen={chartsOpen}
            onToggleCharts={() => setChartsOpen((v) => !v)}
            eventLogOpen={eventLogOpen}
            onToggleEventLog={() => setEventLogOpen((v) => !v)}
          />
        </Box>

        {/* Control panel slide-out — next to sidebar */}
        {controlPanelOpen && (
          <Box sx={{
            position: "absolute",
            top: 42,
            left: 48,
            zIndex: 24,
            backdropFilter: "blur(8px)",
            bgcolor: "rgba(13, 27, 42, 0.5)",
            borderRight: "1px solid rgba(255,255,255,0.08)",
            borderBottom: "1px solid rgba(255,255,255,0.08)",
            borderRadius: "0 0 8px 0",
            pointerEvents: "auto",
          }}>
            <ControlPanel />
          </Box>
        )}

        {/* Restarting overlay */}
        {restarting && (
          <Box sx={{
            position: "absolute",
            top: 0, left: 0, right: 0, bottom: 0,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            bgcolor: "rgba(0,0,0,0.4)",
            zIndex: 50,
            pointerEvents: "auto",
          }}>
            <Typography variant="h6" sx={{ color: "#fff" }}>Restarting cluster...</Typography>
          </Box>
        )}

        {/* Header — overlay */}
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

        {/* Overlay layer — horizontal split: main content left, event log right */}
        <Box sx={{
          position: "absolute",
          top: 52, left: 48, right: 0, bottom: 0,
          display: "flex",
          pointerEvents: "none",
        }}>
          {/* Left area: inspector, chain tree, charts */}
          <Box sx={{ flex: 1, minWidth: 0, display: "flex", flexDirection: "column" }}>
            {/* Inspector */}
            <Box sx={{ flex: 1, minHeight: 0, position: "relative" }}>
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
              </Box>
            </Box>

            {/* Chain tree — above charts, left-aligned */}
            {networkChainTree.length > 0 && chainTreeOpen && (
              <Box sx={{ flexShrink: 0, display: "flex", flexDirection: "column", alignItems: "flex-start" }}>
                <Box sx={{
                  borderRadius: 1,
                  px: 1,
                  py: 0.5,
                  ml: 1,
                  mb: 0.5,
                  maxWidth: "100%",
                  pointerEvents: "auto",
                  backdropFilter: "blur(6px)",
                }}>
                  <ChainTreeView entries={networkChainTree} tipCounts={networkTipCounts} onSelectNode={useStore.getState().selectNode} />
                </Box>
              </Box>
            )}

            {/* Charts — bottom */}
            {chartsOpen && (
              <Box sx={{ flexShrink: 0, display: "flex", flexDirection: "column" }}>
                <Box sx={{
                  height: 200,
                  overflow: "hidden",
                  backdropFilter: "blur(8px)",
                  bgcolor: "rgba(18, 18, 24, 0.3)",
                  borderTop: "1px solid rgba(255,255,255,0.08)",
                  pointerEvents: "auto",
                }}>
                  <AggregateCharts />
                </Box>
              </Box>
            )}
          </Box>

          {/* Event log — right side, full height */}
          {eventLogOpen && (
            <Box sx={{ display: "flex", flexShrink: 0, height: "100%" }}>
              <Box sx={{
                width: 350,
                flexShrink: 0,
                backdropFilter: "blur(8px)",
                bgcolor: "rgba(18, 18, 24, 0.3)",
                borderLeft: "1px solid rgba(255,255,255,0.08)",
                display: "flex",
                flexDirection: "column",
                overflow: "hidden",
                pointerEvents: "auto",
              }}>
                <Box sx={{ flex: 1, minHeight: 0 }}>
                  <EventLog />
                </Box>
              </Box>
            </Box>
          )}
        </Box>
      </Box>
    </Box>
  );
}
