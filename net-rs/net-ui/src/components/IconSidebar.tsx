import { Box, IconButton, Tooltip } from "@mui/material";

/** Mini 5-node degree-2 graph (pentagon with edges). */
function ClusterIcon({ active }: { active: boolean }) {
  // Pentagon vertices (r=10, center=12,12 in a 24x24 viewbox)
  const cx = 12, cy = 12, r = 9;
  const pts = Array.from({ length: 5 }, (_, i) => {
    const angle = (-Math.PI / 2) + (2 * Math.PI * i) / 5;
    return { x: cx + r * Math.cos(angle), y: cy + r * Math.sin(angle) };
  });
  // degree-2: each node connects to its two neighbors
  const edges = pts.map((_, i) => [i, (i + 1) % 5]);

  const color = active ? "#90caf9" : "#aaa";

  return (
    <svg width={28} height={28} viewBox="0 0 24 24">
      {edges.map(([a, b], i) => (
        <line
          key={i}
          x1={pts[a].x} y1={pts[a].y}
          x2={pts[b].x} y2={pts[b].y}
          stroke={color} strokeWidth={1.2} opacity={0.6}
        />
      ))}
      {pts.map((p, i) => (
        <circle
          key={i}
          cx={p.x} cy={p.y} r={2.5}
          fill={color}
        />
      ))}
    </svg>
  );
}

interface IconSidebarProps {
  controlPanelOpen: boolean;
  onToggleControlPanel: () => void;
}

export function IconSidebar({ controlPanelOpen, onToggleControlPanel }: IconSidebarProps) {
  return (
    <Box sx={{
      width: 48,
      height: "100%",
      display: "flex",
      flexDirection: "column",
      alignItems: "center",
      pt: 1,
      bgcolor: "rgba(13, 27, 42, 0.6)",
      backdropFilter: "blur(8px)",
      borderRight: "1px solid rgba(255,255,255,0.08)",
    }}>
      <Tooltip title="Cluster config" placement="right">
        <IconButton
          onClick={onToggleControlPanel}
          sx={{
            bgcolor: controlPanelOpen ? "rgba(144, 202, 249, 0.15)" : "transparent",
            "&:hover": { bgcolor: "rgba(144, 202, 249, 0.2)" },
            borderRadius: 1,
            p: 0.75,
          }}
        >
          <ClusterIcon active={controlPanelOpen} />
        </IconButton>
      </Tooltip>
    </Box>
  );
}
