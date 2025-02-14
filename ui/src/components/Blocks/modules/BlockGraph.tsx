import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useCallback, useMemo } from "react";
import { Bar, BarChart, Legend, Tooltip, XAxis, YAxis } from "recharts";

export const BlockGraph: FC = ({ }) => {
  const {
    state: {
      aggregatedData: {
        blocks,
      }
    },
    dispatch,
  } = useSimContext();

  const data = useMemo(() => {
    return blocks.map(b => {
      const praosTx = b.txs.length;
      const leiosTx = b.cert?.eb.ibs.reduce((sum, ib) => sum + ib.txs.length, 0) ?? 0;
      return {
        name: `Slot ${b.slot}`,
        praosTx,
        leiosTx
      };
    })
  }, [blocks]);

  const viewBlock = useCallback((_state: unknown, index: number) => {
    dispatch({
      type: "SET_CURRENT_BLOCK",
      payload: index
    });
  }, [dispatch]);

  return (
    <div className="flex flex-col w-full h-4/5 items-center justify-center">
      <h2 className="font-bold text-xl">Transactions Per Block</h2>
      <BarChart width={640} height={480} data={data}>
        <XAxis dataKey="name" />
        <YAxis />
        <Tooltip />
        <Legend />
        <Bar dataKey="praosTx" stackId="a" name={"TXs in block"} fill="#8884d8" onClick={viewBlock} />
        <Bar dataKey="leiosTx" stackId="a" name={"TXs from Leios"} fill="#82ca9d" onClick={viewBlock} />
      </BarChart>
    </div>
  )

}