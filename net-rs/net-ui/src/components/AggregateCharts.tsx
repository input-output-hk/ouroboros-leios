import { useMemo } from "react";
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

function formatBytes(b: number): string {
  if (b < 1024) return `${b} B`;
  if (b < 1024 * 1024) return `${(b / 1024).toFixed(0)} KB`;
  return `${(b / 1024 / 1024).toFixed(1)} MB`;
}

const WINDOW = 60;

function padSeries(series: { t: number; value: number | null }[]): { t: number; value: number | null }[] {
  if (series.length >= WINDOW) return series;
  const pad: { t: number; value: number | null }[] = Array.from(
    { length: WINDOW - series.length },
    (_, i) => ({ t: i, value: null }),
  );
  return [...pad, ...series.map((p, i) => ({ ...p, t: WINDOW - series.length + i }))];
}

export function AggregateCharts() {
  const series = useStore((s) => s.aggregateSeries);

  const bwData = useMemo(
    () => padSeries(series.map((p, i) => ({ t: i, value: p.bandwidth / (1024 * 1024) }))),
    [series],
  );
  const msgData = useMemo(
    () => padSeries(series.map((p, i) => ({ t: i, value: p.messages }))),
    [series],
  );
  const blkData = useMemo(
    () => padSeries(series.map((p, i) => ({ t: i, value: p.blocks }))),
    [series],
  );

  if (series.length < 2) {
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
    <Box sx={{ display: "flex", height: "100%", "& > :not(:last-child)": { borderRight: 1, borderColor: "grey.800" } }}>
      <ChartCard
        title="Bandwidth/s"
        data={bwData}
        color="#90caf9"
        formatValue={(v) => formatBytes(v * 1024 * 1024) + "/s"}
      />
      <ChartCard
        title="Messages"
        data={msgData}
        color="#f48fb1"
        formatValue={(v) => String(Math.round(v))}
      />
      <ChartCard
        title="Blocks"
        data={blkData}
        color="#a5d6a7"
        formatValue={(v) => String(Math.round(v))}
      />
    </Box>
  );
}

function ChartCard({
  title,
  data,
  color,
  formatValue,
}: {
  title: string;
  data: { t: number; value: number | null }[];
  color: string;
  formatValue: (v: number) => string;
}) {
  return (
    <Box sx={{ flex: 1, minWidth: 0, p: 1 }}>
      <Typography variant="body2" color="text.secondary">
        {title}
      </Typography>
      <ResponsiveContainer width="100%" height="85%">
        <LineChart data={data}>
          <XAxis dataKey="t" hide />
          <YAxis
            width={55}
            tick={{ fontSize: 10 }}
            tickFormatter={(v: number) => formatValue(v)}
          />
          <Tooltip formatter={(v: number) => formatValue(v)} />
          <Line
            type="monotone"
            dataKey="value"
            stroke={color}
            dot={false}
            strokeWidth={1.5}
            isAnimationActive={false}
            connectNulls={false}
          />
        </LineChart>
      </ResponsiveContainer>
    </Box>
  );
}
