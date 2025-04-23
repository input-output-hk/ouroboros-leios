import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useMemo } from "react";
import { Area, AreaChart, Tooltip, XAxis, YAxis } from "recharts";

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

  return (
    <div className="flex flex-col w-full h-4/5 items-center justify-center">
      <h2 className="font-bold text-xl">Transactions</h2>
      <AreaChart width={640} height={480} data={data}>
        <XAxis dataKey="Time" />
        <YAxis />
        <Tooltip />
        <Area type="monotone" dataKey="Created" stackId="1" stroke="#26de81" fill="#26de81" />
        <Area type="monotone" dataKey="In Input Block" stackId="1" stroke="#2bcbba" fill="#2bcbba" />
        <Area type="monotone" dataKey="In Endorser Block" stackId="1" stroke="#4b7bec" fill="#4b7bec" />
        <Area type="monotone" dataKey="On Chain" stackId="1" stroke="#2d98da" fill="#2d98da" />
      </AreaChart>
    </div>
  );
}