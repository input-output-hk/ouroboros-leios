import { useEffect, useRef } from "react";
import { Box, Typography, IconButton } from "@mui/material";
import PauseIcon from "@mui/icons-material/Pause";
import PlayArrowIcon from "@mui/icons-material/PlayArrow";
import { useStore, getEvents } from "@/store";

const typeColors: Record<string, string> = {
  RBGenerated: "#a5d6a7",
  RBReceived: "#81c784",
  EBGenerated: "#90caf9",
  EBReceived: "#64b5f6",
  VTBundleGenerated: "#ce93d8",
  VTBundleReceived: "#ba68c8",
  RolledBack: "#e040fb",
  Slot: "#fff59d",
};

export function EventLog() {
  const eventVersion = useStore((s) => s.eventVersion);
  const paused = useStore((s) => s.eventsPaused);
  const togglePause = useStore((s) => s.toggleEventsPause);
  const bottomRef = useRef<HTMLDivElement>(null);
  const events = getEvents();

  useEffect(() => {
    if (!paused) {
      bottomRef.current?.scrollIntoView();
    }
  }, [eventVersion, paused]);

  return (
    <Box sx={{ height: "100%", display: "flex", flexDirection: "column" }}>
      <Box sx={{ display: "flex", alignItems: "center", px: 1, py: 0.25, borderBottom: 1, borderColor: "grey.800" }}>
        <Typography variant="caption" color="text.secondary" sx={{ flex: 1 }}>
          Events {paused && "(paused)"}
        </Typography>
        <IconButton size="small" onClick={togglePause} sx={{ p: 0.25 }}>
          {paused ? <PlayArrowIcon sx={{ fontSize: 16 }} /> : <PauseIcon sx={{ fontSize: 16 }} />}
        </IconButton>
      </Box>
      <div
        style={{
          flex: 1,
          overflowY: "auto",
          padding: 8,
          fontFamily: "monospace",
          fontSize: 13,
          minHeight: 0,
        }}
      >
      {events.length === 0 && (
        <Typography color="text.secondary" variant="body2">
          Waiting for events...
        </Typography>
      )}
      {events.map((e, i) => {
        const msgType = e.message?.type ?? "unknown";
        const color = typeColors[msgType] ?? "#999";
        return (
          <div key={i} style={{ display: "flex", gap: 4, marginBottom: 2, alignItems: "center" }}>
            <span style={{ minWidth: 55, color: "#999" }}>
              {e.time_s.toFixed(1)}s
            </span>
            <span style={{ width: 55, flexShrink: 0 }}>
              {e.message?.node ?? "?"}
            </span>
            <span
              style={{
                fontSize: 11,
                padding: "1px 5px",
                borderRadius: 8,
                backgroundColor: `${color}22`,
                color,
                border: `1px solid ${color}`,
              }}
            >
              {msgType}
            </span>
          </div>
        );
      })}
      <div ref={bottomRef} />
      </div>
    </Box>
  );
}
