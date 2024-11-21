"use client";

import { useGraphContext } from "@/contexts/GraphContext/context";

export const Test = () => {
  const { topography, transactions, messages, currentTime, maxTime } = useGraphContext();

  return (
    <p>
      Nodes: {topography.nodes.size}<br/>
      Links: {topography.links.size}<br/>
      Total Events: {messages.length}<br/>
      Transaction List: {transactions.size}<br/>
      Current Time: {currentTime}<br/>
      Max Time: {maxTime}
    </p>
  );
}
