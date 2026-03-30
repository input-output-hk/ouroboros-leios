import { Box, Typography, Divider, Chip } from "@mui/material";
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  ResponsiveContainer,
} from "recharts";
import { useStore } from "@/store";

function formatBytes(b: number): string {
  if (b < 1024) return `${b} B`;
  if (b < 1024 * 1024) return `${(b / 1024).toFixed(1)} KB`;
  return `${(b / 1024 / 1024).toFixed(1)} MB`;
}

function NodeInspector({ nodeId }: { nodeId: string }) {
  const stats = useStore((s) => s.latestStats[nodeId]);
  const series = useStore((s) => s.nodeTimeSeries[nodeId] ?? []);

  const chartData = series.map((p, i) => ({
    t: i,
    bandwidth: p.bandwidth,
    messages: p.messages,
  }));

  return (
    <Box>
      <Typography variant="subtitle2" color="primary" gutterBottom>
        {nodeId}
      </Typography>

      {stats ? (
        <Box sx={{ mb: 1 }}>
          <Typography variant="body2">Slot: {stats.slot}</Typography>
          <Typography variant="body2">
            Tip: {stats.tip_block_no ?? "—"}
          </Typography>
          <Typography variant="body2">
            Blocks: {stats.blocks_produced} produced, {stats.blocks_received}{" "}
            received
          </Typography>
          <Typography variant="body2">
            TXs generated: {stats.txs_generated}
          </Typography>
          <Typography variant="body2">
            Uptime: {stats.uptime_secs.toFixed(0)}s
          </Typography>

          <Divider sx={{ my: 1 }} />
          <Typography variant="caption" color="text.secondary">
            Peers ({stats.peer_count})
          </Typography>
          {stats.peers.map((p) => (
            <Box key={p.peer_id} sx={{ ml: 1, mb: 0.5 }}>
              <Typography variant="body2" fontSize={11}>
                <Chip label={p.mode} size="small" sx={{ mr: 0.5, height: 16, fontSize: 10 }} />
                {p.address}
                {p.rtt_ms != null && ` (${p.rtt_ms.toFixed(0)}ms RTT)`}
              </Typography>
              <Typography variant="body2" fontSize={10} color="text.secondary" sx={{ ml: 1 }}>
                {formatBytes(p.bytes_sent)} sent / {formatBytes(p.bytes_received)} received
              </Typography>
            </Box>
          ))}
        </Box>
      ) : (
        <Typography variant="body2" color="text.secondary">
          No stats yet
        </Typography>
      )}

      {chartData.length > 1 && (
        <>
          <Divider sx={{ my: 1 }} />
          <Typography variant="caption" color="text.secondary">
            Bandwidth
          </Typography>
          <ResponsiveContainer width="100%" height={80}>
            <LineChart data={chartData}>
              <XAxis dataKey="t" hide />
              <YAxis hide />
              <Tooltip />
              <Line
                type="monotone"
                dataKey="bandwidth"
                stroke="#90caf9"
                dot={false}
                strokeWidth={1.5}
              />
            </LineChart>
          </ResponsiveContainer>

          <Typography variant="caption" color="text.secondary">
            Messages
          </Typography>
          <ResponsiveContainer width="100%" height={80}>
            <LineChart data={chartData}>
              <XAxis dataKey="t" hide />
              <YAxis hide />
              <Tooltip />
              <Line
                type="monotone"
                dataKey="messages"
                stroke="#f48fb1"
                dot={false}
                strokeWidth={1.5}
              />
            </LineChart>
          </ResponsiveContainer>
        </>
      )}
    </Box>
  );
}

function EdgeInspector({ from, to }: { from: number; to: number }) {
  const topology = useStore((s) => s.topology);
  const edge = topology?.edges.find((e) => e.from === from && e.to === to);

  if (!topology || !edge) return null;

  const srcNode = topology.nodes[from];
  const dstNode = topology.nodes[to];

  return (
    <Box>
      <Typography variant="subtitle2" color="primary" gutterBottom>
        Edge: {srcNode?.node_id} — {dstNode?.node_id}
      </Typography>
      <Typography variant="body2">Latency: {edge.latency_ms}ms</Typography>
      <Typography variant="body2">
        {srcNode?.listen_address} ↔ {dstNode?.listen_address}
      </Typography>
    </Box>
  );
}

export function InspectorPanel() {
  const selectedNodeId = useStore((s) => s.selectedNodeId);
  const selectedEdge = useStore((s) => s.selectedEdge);

  if (!selectedNodeId && !selectedEdge) {
    return (
      <Box sx={{ p: 2 }}>
        <Typography variant="body2" color="text.secondary">
          Click a node or edge to inspect
        </Typography>
      </Box>
    );
  }

  return (
    <Box sx={{ p: 2, overflowY: "auto", height: "100%" }}>
      {selectedNodeId && <NodeInspector nodeId={selectedNodeId} />}
      {selectedEdge && (
        <EdgeInspector from={selectedEdge.from} to={selectedEdge.to} />
      )}
    </Box>
  );
}
