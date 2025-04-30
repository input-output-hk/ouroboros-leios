import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useMemo } from "react";
import { Area, AreaChart, ResponsiveContainer, Tooltip, XAxis, YAxis } from "recharts";

export const TransactionsView: FC = ({ }) => {
  const {
    state: {
      aggregatedData: {
        transactions,
      }
    },
  } = useSimContext();

  const data = useMemo(() => {
    return transactions.map(data => {
      const minutes = Math.floor(data.timestamp / 60);
      const seconds = Math.floor(data.timestamp % 60);
      return {
        Time: minutes ? `${minutes}m${seconds}s` : `${seconds}s`,
        "Created": data.created,
        "In Input Block": data.inIb,
        "In Endorser Block": data.inEb,
        "On Chain": data.onChain,
      };
    })
  }, [transactions]);

  const tooltipOrderer = ["Created", "In Input Block", "In Endorser Block", "On Chain"];

  return (
    <div className="flex flex-col w-full h-4/5 items-center justify-center">
      <h2 className="font-bold text-xl">Transactions</h2>
      <ResponsiveContainer width="80%" height="80%">
        <AreaChart data={data}>
          <XAxis dataKey="Time" />
          <YAxis />
          <Tooltip itemSorter={i => tooltipOrderer.indexOf(i.dataKey as string)} />
          <Area type="monotone" dataKey="On Chain" stackId="1" isAnimationActive={false} stroke="#9e0142" fill="#9e0142" />
          <Area type="monotone" dataKey="In Endorser Block" stackId="1" isAnimationActive={false} stroke="#d0394e" fill="#d0394e" />
          <Area type="monotone" dataKey="In Input Block" stackId="1" isAnimationActive={false} stroke="#ef6445" fill="#ef6445" />
          <Area type="monotone" dataKey="Created" stackId="1" isAnimationActive={false} stroke="#fb9d56" fill="#fb9d56" />
        </AreaChart>
      </ResponsiveContainer>
    </div>
  );
}