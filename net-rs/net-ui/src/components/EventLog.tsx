import { useEffect, useRef } from "react";
import { Box, Typography, Chip, IconButton } from "@mui/material";
import PauseIcon from "@mui/icons-material/Pause";
import PlayArrowIcon from "@mui/icons-material/PlayArrow";
import { useStore } from "@/store";

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
  const events = useStore((s) => s.events);
  const paused = useStore((s) => s.eventsPaused);
  const togglePause = useStore((s) => s.toggleEventsPause);
  const bottomRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!paused) {
      bottomRef.current?.scrollIntoView({ behavior: "smooth" });
    }
  }, [events.length, paused]);

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
      <Box
        sx={{
          flex: 1,
          overflowY: "auto",
          p: 1,
          fontFamily: "monospace",
          fontSize: 16,
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
          <Box key={i} sx={{ display: "flex", gap: 0.5, mb: 0.25, alignItems: "center" }}>
            <Typography variant="caption" color="text.secondary" sx={{ minWidth: 55 }}>
              {e.time_s.toFixed(1)}s
            </Typography>
            <Typography variant="caption" sx={{ minWidth: 45 }}>
              {e.message?.node ?? "?"}
            </Typography>
            <Chip
              label={msgType}
              size="small"
              sx={{
                height: 16,
                fontSize: 9,
                bgcolor: `${color}22`,
                color,
                borderColor: color,
                border: "1px solid",
              }}
            />
          </Box>
        );
      })}
      <div ref={bottomRef} />
      </Box>
    </Box>
  );
}
