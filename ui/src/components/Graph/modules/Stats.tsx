import { FC, useMemo } from "react";

import { useGraphContext } from "@/contexts/GraphContext/context";

export const Stats: FC = () => {
  const {
    state: { aggregatedData, currentNode },
  } = useGraphContext();

  const currentNodeStats = useMemo(() => {
    return currentNode
      ? aggregatedData.current.nodes.get(currentNode)
      : undefined;
  }, [currentNode]);

  return (
    <div className="flex flex-col gap-4">
      <div className="border-2 border-gray-200 rounded p-4">
        <h2>Total Stats</h2>
        <h4>
          Transactions Generated: {aggregatedData.current.total.txGenerated}
        </h4>
        <h4>Propagations: {aggregatedData.current.total.txPropagations}</h4>
      </div>
      <div className="border-2 border-gray-200 rounded p-4">
      <h2>Node Stats ({currentNode ? `ID: #${currentNode}` : "Not Selected"})</h2>
      {currentNodeStats && (
        <>
          <h4>Tx Generated: {currentNodeStats?.txGenerated}</h4>
          <h4>Tx Propagations: {currentNodeStats?.txPropagations}</h4>
          <h4>EB Generated: {currentNodeStats?.ebGenerated}</h4>
          <h4>EB Sent: {currentNodeStats?.ebSent}</h4>
          <h4>EB Received: {currentNodeStats?.ebReceived}</h4>
          <h4>IB Generated: {currentNodeStats?.ibGenerated}</h4>
          <h4>IB Sent: {currentNodeStats?.ibSent}</h4>
          <h4>IB Received: {currentNodeStats?.ibReceived}</h4>
          <h4>PB Generated: {currentNodeStats?.pbGenerated}</h4>
          <h4>PB Sent: {currentNodeStats?.pbSent}</h4>
          <h4>PB Received: {currentNodeStats?.pbReceived}</h4>
          <h4>PB Sent: {currentNodeStats?.pbSent}</h4>
          <h4>PB Received: {currentNodeStats?.pbReceived}</h4>
        </>
        )}
      </div>
    </div>
  );
};
