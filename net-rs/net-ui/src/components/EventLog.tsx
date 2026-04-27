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
  VotesReceived: "#ba68c8",
  RolledBack: "#e040fb",
  Slot: "#fff59d",
  TipAdvanced: "#80cbc4",
  BlockValidated: "#aed581",
  PeerConnected: "#90a4ae",
  PeerDisconnected: "#90a4ae",
  TXGenerated: "#fff59d",
  LeiosQuorumReached: "#ffb74d",
  LeiosElectionExpired: "#bcaaa4",
  RbCertifiedEb: "#ffd54f",
};

const DEFAULT_COLOR = "#999999";
const HIGHLIGHT_TYPES = new Set(["RbCertifiedEb"]);

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
        const color = typeColors[msgType] ?? DEFAULT_COLOR;
        const highlight = HIGHLIGHT_TYPES.has(msgType);
        return (
          <div key={i} style={{ display: "flex", gap: 4, marginBottom: 2, alignItems: "center" }}>
            <span style={{ minWidth: 55, color: "#999999" }}>
              {e.time_s.toFixed(1)}s
            </span>
            <span style={{ width: 72, flexShrink: 0, whiteSpace: "nowrap" }}>
              {e.message?.node ?? "?"}
            </span>
            <span
              style={{
                fontSize: highlight ? 12 : 11,
                fontWeight: highlight ? 700 : 400,
                padding: highlight ? "2px 7px" : "1px 5px",
                borderRadius: 8,
                backgroundColor: highlight ? `${color}55` : `${color}22`,
                color,
                border: `${highlight ? 2 : 1}px solid ${color}`,
                boxShadow: highlight ? `0 0 6px ${color}88` : undefined,
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
