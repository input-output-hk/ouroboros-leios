import { FC } from "react";

import { useSimContext } from "@/contexts/SimContext/context";
import { ISimulationAggregatedTotalData } from "@/contexts/SimContext/types";
import { useTimelineAggregation } from "@/hooks/useTimelineAggregation";

export const Stats: FC = () => {
  const {
    state: { aggregatedData },
  } = useSimContext();

  const timelineInfo = useTimelineAggregation();

  const totals = [...aggregatedData.nodes].reduce(
    (total, [_id, data]) => {
      (["tx", "pb", "ib", "eb", "votes"] as const).forEach((type) => {
        const generatedKey = (type +
          "Generated") as keyof ISimulationAggregatedTotalData;
        total[generatedKey] += data.generated[type] ?? 0;
        const propagatedKey = (type +
          "Propagations") as keyof ISimulationAggregatedTotalData;
        total[propagatedKey] += data.received[type]?.count ?? 0;
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
      ...aggregatedData.global,
    } as ISimulationAggregatedTotalData,
  );

  return (
    <div
      className={`flex flex-col gap-4 backdrop-blur-xs bg-white/80 text-xl min-w-[300px]`}
    >
      <div className="border-2 border-gray-200 rounded-sm p-4">
        <h2 className="font-bold uppercase mb-2">Global Stats</h2>
        
        {/* Timeline Info */}
        <div className="mb-4 pb-4 border-b border-gray-300">
          <h3 className="text-lg font-semibold mb-2">Timeline</h3>
          <div className="text-base">
            <h4 className="flex items-center justify-between gap-4">
              Current Time: <span>{timelineInfo.currentTime.toFixed(2)}s</span>
            </h4>
            <h4 className="flex items-center justify-between gap-4">
              Total Events: <span>{timelineInfo.totalEvents}</span>
            </h4>
            <h4 className="flex items-center justify-between gap-4">
              Events at Time: <span>{timelineInfo.eventCounts.total}</span>
            </h4>
            {Object.keys(timelineInfo.eventCounts.byType).length > 0 && (
              <div className="text-sm mt-2">
                <h5 className="font-semibold">Event Types:</h5>
                {Object.entries(timelineInfo.eventCounts.byType).map(
                  ([type, count]) => (
                    <div key={type} className="flex justify-between text-sm">
                      <span>{type}:</span> <span>{count}</span>
                    </div>
                  ),
                )}
              </div>
            )}
          </div>
        </div>

        {/* Aggregated Stats */}
        <h4 className="flex items-center justify-between gap-4">
          Tx Generated: <span>{totals.txGenerated}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Tx Propagations: <span>{totals.txPropagations}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          IB Generated: <span>{totals.ibGenerated}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          IB Propagations: <span>{totals.ibPropagations}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          EB Generated: <span>{totals.ebGenerated}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          EB Propagations: <span>{totals.ebPropagations}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Blocks Generated: <span>{totals.pbGenerated}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Block Propagations: <span>{totals.pbPropagations}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Vote Bundles Generated: <span>{totals.votesGenerated}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Vote Bundle Propagations: <span>{totals.votesPropagations}</span>
        </h4>
        <br />
        <h4 className="flex items-center justify-between gap-4">
          Transactions On-Chain Directly<span>{totals.praosTxOnChain}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Transactions On-Chain from Leios<span>{totals.leiosTxOnChain}</span>
        </h4>
      </div>
    </div>
  );
};
