"use client";

import { FC, useMemo } from "react";
import {
  Area,
  AreaChart,
  CartesianGrid,
  ResponsiveContainer,
  Tooltip,
  TooltipProps,
  XAxis,
  YAxis,
} from "recharts";
import { NameType, ValueType } from "recharts/types/component/DefaultTooltipContent";

import { useGraphContext } from "@/contexts/GraphContext/context";

const CustomTooltip = ({
  active,
  payload,
  label,
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
  const { state: { maxTime, sentTxs } } = useGraphContext();

  const data = useMemo(
    () =>
      [...sentTxs.values()].map((v, index) => ({
        message: index + 1,
        time: Number(v.split("#")[1]),
      })),
    [sentTxs.size],
  );

  return (
    <ResponsiveContainer width="100%" height="100%">
      <AreaChart data={data}>
        <CartesianGrid strokeDasharray="3 3" />
        <XAxis
          tick={false}
          label="Transactions Sent"
          allowDataOverflow
          type="number"
          dataKey="message"
        />
        <YAxis tick={false} label="Time" domain={[0, maxTime]} dataKey="time" />
        <Area
          type="monotone"
          dataKey="time"
          stroke="#8884d8"
          fill="#8884d8"
          strokeWidth={2}
          dot={false}
        />
        <Tooltip content={(props) => <CustomTooltip {...props} />} />
      </AreaChart>
    </ResponsiveContainer>
  );
};
