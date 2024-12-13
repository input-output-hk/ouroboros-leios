import { FC } from "react";

import { useGraphContext } from "@/contexts/GraphContext/context";
import {
  ISimulationAggregatedData,
  ISimulationAggregatedTotalData,
} from "@/contexts/GraphContext/types";

export const Stats: FC = () => {
  const {
    state: { aggregatedData },
  } = useGraphContext();

  const totals = [...aggregatedData.nodes].reduce(
    (total, [_id, data]) => {
      (
        Object.entries(data) as unknown as [
          keyof ISimulationAggregatedData,
          number,
        ][]
      ).forEach(([key, value]) => {
        if (
          key === "txGenerated" ||
          key === "ebGenerated" ||
          key === "ibGenerated" ||
          key === "pbGenerated" ||
          key === "votesGenerated"
        ) {
          total[key] += value;
        }

        if (
          key === "txReceived" ||
          key === "ebReceived" ||
          key === "ibReceived" ||
          key === "pbReceived" ||
          key === "votesReceived"
        ) {
          total[key.replace("Received", "Propagations") as keyof ISimulationAggregatedTotalData] += value;
        }
      });

      return total;
    },
    {
      ebGenerated: 0,
      ebPropagations: 0,
      ibGenerated: 0,
      ibPropagations: 0,
      pbGenerated: 0,
      pbPropagations: 0,
      txGenerated: 0,
      txPropagations: 0,
      votesGenerated: 0,
      votesPropagations: 0,
    } as ISimulationAggregatedTotalData,
  );

  return (
    <div className={`flex flex-col gap-4 backdrop-blur-sm bg-white/80 min-w-[300px]`}>
      <div className="border-2 border-gray-200 rounded p-4">
        <h2 className="font-bold uppercase mb-2">Global Stats</h2>
        <h4 className="flex items-center justify-between gap-4">Tx Generated: <span>{totals.txGenerated}</span></h4>
        <h4 className="flex items-center justify-between gap-4">Tx Propagations: <span>{totals.txPropagations}</span></h4>
        <h4 className="flex items-center justify-between gap-4">IB Generated: <span>{totals.ibGenerated}</span></h4>
        <h4 className="flex items-center justify-between gap-4">IB Propagations: <span>{totals.ibPropagations}</span></h4>
        <h4 className="flex items-center justify-between gap-4">EB Generated: <span>{totals.ebGenerated}</span></h4>
        <h4 className="flex items-center justify-between gap-4">EB Propagations: <span>{totals.ebPropagations}</span></h4>
        <h4 className="flex items-center justify-between gap-4">PB Generated: <span>{totals.pbGenerated}</span></h4>
        <h4 className="flex items-center justify-between gap-4">PB Propagations: <span>{totals.pbPropagations}</span></h4>
        <h4 className="flex items-center justify-between gap-4">Votes Generated: <span>{totals.votesGenerated}</span></h4>
        <h4 className="flex items-center justify-between gap-4">Votes Propagations: <span>{totals.votesPropagations}</span></h4>
      </div>
    </div>
  );
};
