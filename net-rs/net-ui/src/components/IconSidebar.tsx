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

/** Chain tree: 3 main blocks in a row with a fork block diagonally
 *  off the middle block (child in the next column, next lane down),
 *  matching ChainTreeView's outlined-rectangle style. */
function ChainTreeIcon({ active }: { active: boolean }) {
  const mainColor = active ? "#90caf9" : "#8a8a8a";
  const forkColor = active ? "#ffb74d" : "#6a6a6a";
  const lineColor = active ? "#888" : "#555";
  const fill = "rgba(30,30,30,0.8)";
  const bw = 6;
  const bh = 5;
  // Main row at y=5..10, fork row at y=14..19
  const mainY = 5;
  const forkY = 14;
  // Columns — fork shares col 2 (where the middle block's child goes)
  const xs = [1, 8.5, 16];
  const midY = mainY + bh / 2;
  const forkMidY = forkY + bh / 2;
  return (
    <svg width={28} height={28} viewBox="0 0 24 24">
      {/* main-chain connectors (horizontal, right edge -> left edge) */}
      <line x1={xs[0] + bw} y1={midY} x2={xs[1]} y2={midY} stroke={lineColor} strokeWidth={1.3} />
      <line x1={xs[1] + bw} y1={midY} x2={xs[2]} y2={midY} stroke={lineColor} strokeWidth={1.3} />
      {/* fork connector — diagonal from middle block right edge to fork left edge */}
      <line x1={xs[1] + bw} y1={midY} x2={xs[2]} y2={forkMidY} stroke={lineColor} strokeWidth={1.3} />
      {/* main blocks */}
      {xs.map((x, i) => (
        <rect key={i} x={x} y={mainY} width={bw} height={bh} rx={1.2} fill={fill} stroke={mainColor} strokeWidth={1.3} />
      ))}
      {/* fork block (col 2, lane 1) */}
      <rect x={xs[2]} y={forkY} width={bw} height={bh} rx={1.2} fill={fill} stroke={forkColor} strokeWidth={1.3} />
    </svg>
  );
}

/** Spiky line chart. */
function ChartIcon({ active }: { active: boolean }) {
  const color = active ? "#90caf9" : "#aaa";
  // jagged path with spikes
  const pts = "2,18 5,12 7,16 10,6 13,14 16,4 19,15 22,10";
  return (
    <svg width={28} height={28} viewBox="0 0 24 24">
      {/* baseline axis */}
      <line x1={2} y1={21} x2={22} y2={21} stroke={color} strokeWidth={1} opacity={0.4} />
      <polyline points={pts} fill="none" stroke={color} strokeWidth={1.5} strokeLinejoin="round" strokeLinecap="round" />
    </svg>
  );
}

/** Document icon with lines (event log). */
function EventLogIcon({ active }: { active: boolean }) {
  const color = active ? "#90caf9" : "#aaa";
  return (
    <svg width={28} height={28} viewBox="0 0 24 24">
      {/* page outline with a folded corner */}
      <path
        d="M 6 3 L 16 3 L 20 7 L 20 21 L 6 21 Z"
        fill="none"
        stroke={color}
        strokeWidth={1.4}
        strokeLinejoin="round"
      />
      <path d="M 16 3 L 16 7 L 20 7" fill="none" stroke={color} strokeWidth={1.4} strokeLinejoin="round" />
      {/* text lines */}
      <line x1={9} y1={11} x2={17} y2={11} stroke={color} strokeWidth={1.2} />
      <line x1={9} y1={14} x2={17} y2={14} stroke={color} strokeWidth={1.2} />
      <line x1={9} y1={17} x2={14} y2={17} stroke={color} strokeWidth={1.2} />
    </svg>
  );
}

interface IconSidebarProps {
  controlPanelOpen: boolean;
  onToggleControlPanel: () => void;
  chainTreeOpen: boolean;
  onToggleChainTree: () => void;
  chartsOpen: boolean;
  onToggleCharts: () => void;
  eventLogOpen: boolean;
  onToggleEventLog: () => void;
}

export function IconSidebar({
  controlPanelOpen,
  onToggleControlPanel,
  chainTreeOpen,
  onToggleChainTree,
  chartsOpen,
  onToggleCharts,
  eventLogOpen,
  onToggleEventLog,
}: IconSidebarProps) {
  const buttonSx = (active: boolean) => ({
    bgcolor: active ? "rgba(144, 202, 249, 0.15)" : "transparent",
    "&:hover": { bgcolor: "rgba(144, 202, 249, 0.2)" },
    borderRadius: 1,
    p: 0.75,
  });

  return (
    <Box sx={{
      width: 48,
      height: "100%",
      display: "flex",
      flexDirection: "column",
      alignItems: "center",
      pt: 1,
      gap: 0.5,
      bgcolor: "rgba(13, 27, 42, 0.6)",
      backdropFilter: "blur(8px)",
      borderRight: "1px solid rgba(255,255,255,0.08)",
    }}>
      <Tooltip title="Cluster config" placement="right">
        <IconButton onClick={onToggleControlPanel} sx={buttonSx(controlPanelOpen)}>
          <ClusterIcon active={controlPanelOpen} />
        </IconButton>
      </Tooltip>
      <Tooltip title="Chain tree" placement="right">
        <IconButton onClick={onToggleChainTree} sx={buttonSx(chainTreeOpen)}>
          <ChainTreeIcon active={chainTreeOpen} />
        </IconButton>
      </Tooltip>
      <Tooltip title="Charts" placement="right">
        <IconButton onClick={onToggleCharts} sx={buttonSx(chartsOpen)}>
          <ChartIcon active={chartsOpen} />
        </IconButton>
      </Tooltip>
      <Tooltip title="Event log" placement="right">
        <IconButton onClick={onToggleEventLog} sx={buttonSx(eventLogOpen)}>
          <EventLogIcon active={eventLogOpen} />
        </IconButton>
      </Tooltip>
    </Box>
  );
}
