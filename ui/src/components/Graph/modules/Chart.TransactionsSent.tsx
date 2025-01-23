"use client";

import { FC, useMemo } from "react";
import {
  CartesianGrid,
  Line,
  LineChart,
  ResponsiveContainer,
  Tooltip,
  TooltipProps,
  XAxis,
  YAxis,
} from "recharts";
import {
  NameType,
  ValueType,
} from "recharts/types/component/DefaultTooltipContent";

import { useSimContext } from "@/contexts/SimContext/context";

const CustomTooltip = ({
  active,
  payload,
}: TooltipProps<ValueType, NameType>) => {
  if (active && payload && payload.length) {
    return (
      <div className="custom-tooltip">
        <p className="label">{`Message: #${payload[0].payload.message}`}</p>
        <p className="intro">{`Time Sent: ${payload[0].payload.time}ms`}</p>
      </div>
    );
  }

  return null;
};

export const ChartTransactionsSent: FC = () => {
  const {
    state: { maxTime, sentTxs },
  } = useSimContext();

  const data = useMemo(() => {
    return sentTxs.sort((a, b) => a - b).map((v, index) => ({
      message: index + 1,
      time: v,
    }));
  }, [sentTxs]);

  return (
    <ResponsiveContainer width="100%" height="100%">
      <LineChart data={data}>
        <CartesianGrid strokeDasharray={2} />
        <YAxis
          tick={false}
          label={{
            value: "Tx Propagations",
            angle: -90,
          }}
          domain={[0, Math.max(sentTxs.length, 1000)]}
          allowDataOverflow
          type="number"
          dataKey="message"
        />
        <XAxis
          tickFormatter={(v) => `${v.toFixed(0)}ms`}
          label="Time"
          type="number"
          tickCount={2}
          allowDataOverflow
          domain={[0, maxTime]}
          dataKey="time"
        />
        <Line
          type="natural"
          dataKey="message"
          stroke="#8884d8"
          strokeWidth={2}
          dot={false}
        />
        <Tooltip content={(props) => <CustomTooltip {...props} />} />
      </LineChart>
    </ResponsiveContainer>
  );
};
