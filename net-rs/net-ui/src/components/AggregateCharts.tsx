import { Box, Typography } from "@mui/material";
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  ResponsiveContainer,
} from "recharts";
import { useStore } from "@/store";

export function AggregateCharts() {
  const series = useStore((s) => s.aggregateSeries);

  const data = series.map((p, i) => ({
    t: i,
    bandwidth: p.bandwidth,
    messages: p.messages,
    blocks: p.blocks,
  }));

  if (data.length < 2) {
    return (
      <Box
        sx={{
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          height: "100%",
        }}
      >
        <Typography color="text.secondary">Waiting for stats...</Typography>
      </Box>
    );
  }

  return (
    <Box sx={{ display: "flex", gap: 1, height: "100%", p: 1 }}>
      <ChartCard title="Bandwidth (bytes)" dataKey="bandwidth" data={data} color="#90caf9" />
      <ChartCard title="Messages" dataKey="messages" data={data} color="#f48fb1" />
      <ChartCard title="Blocks Produced" dataKey="blocks" data={data} color="#a5d6a7" />
    </Box>
  );
}

function ChartCard({
  title,
  dataKey,
  data,
  color,
}: {
  title: string;
  dataKey: string;
  data: Record<string, number>[];
  color: string;
}) {
  return (
    <Box sx={{ flex: 1, minWidth: 0 }}>
      <Typography variant="caption" color="text.secondary" sx={{ pl: 1 }}>
        {title}
      </Typography>
      <ResponsiveContainer width="100%" height="85%">
        <LineChart data={data}>
          <XAxis dataKey="t" hide />
          <YAxis width={50} tick={{ fontSize: 10 }} />
          <Tooltip />
          <Line
            type="monotone"
            dataKey={dataKey}
            stroke={color}
            dot={false}
            strokeWidth={1.5}
            isAnimationActive={false}
          />
        </LineChart>
      </ResponsiveContainer>
    </Box>
  );
}
