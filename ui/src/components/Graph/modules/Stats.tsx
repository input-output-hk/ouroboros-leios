import { FC, useMemo } from "react";

import { useGraphContext } from "@/contexts/GraphContext/context";
import {
  ISimulationAggregatedData,
  ISimulationAggregatedTotalData,
} from "@/contexts/GraphContext/types";

export const Stats: FC = () => {
  const {
    state: { aggregatedData, currentNode },
  } = useGraphContext();

  const currentNodeStats = useMemo(() => {
    return currentNode
      ? aggregatedData.nodes.get(currentNode)
      : undefined;
  }, [currentNode]);

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
    <div className="flex flex-col gap-4">
      <div className="border-2 border-gray-200 rounded p-4">
        <h2 className="font-bold">Total Stats</h2>
        <h4>Tx Generated: {totals.txGenerated}</h4>
        <h4>Tx Propagations: {totals.txPropagations}</h4>
        <h4>IB Generated: {totals.ibGenerated}</h4>
        <h4>IB Propagations: {totals.ibPropagations}</h4>
        <h4>EB Generated: {totals.ebGenerated}</h4>
        <h4>EB Propagations: {totals.ebPropagations}</h4>
        <h4>PB Generated: {totals.pbGenerated}</h4>
        <h4>PB Propagations: {totals.pbPropagations}</h4>
        <h4>Votes Generated: {totals.votesGenerated}</h4>
        <h4>Votes Propagations: {totals.votesPropagations}</h4>
      </div>
      <div className="border-2 border-gray-200 rounded p-4">
        <h2>
          Node Stats ({currentNode ? `ID: #${currentNode}` : "Not Selected"})
        </h2>
        {currentNodeStats && (
          <>
            <h4>Tx Generated: {currentNodeStats?.txGenerated}</h4>
            <h4>Tx Sent: {currentNodeStats?.txSent}</h4>
            <h4>Tx Received: {currentNodeStats?.txReceived}</h4>
            <h4>EB Generated: {currentNodeStats?.ebGenerated}</h4>
            <h4>EB Sent: {currentNodeStats?.ebSent}</h4>
            <h4>EB Received: {currentNodeStats?.ebReceived}</h4>
            <h4>IB Generated: {currentNodeStats?.ibGenerated}</h4>
            <h4>IB Sent: {currentNodeStats?.ibSent}</h4>
            <h4>IB Received: {currentNodeStats?.ibReceived}</h4>
            <h4>PB Generated: {currentNodeStats?.pbGenerated}</h4>
            <h4>PB Sent: {currentNodeStats?.pbSent}</h4>
            <h4>PB Received: {currentNodeStats?.pbReceived}</h4>
            <h4>Votes Generated: {currentNodeStats?.votesGenerated}</h4>
            <h4>Votes Sent: {currentNodeStats?.votesSent}</h4>
            <h4>Votes Received: {currentNodeStats?.votesReceived}</h4>
          </>
        )}
      </div>
    </div>
  );
};
