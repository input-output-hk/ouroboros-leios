"use client";

import { useGraphContext } from "@/contexts/GraphContext/context";

export const Test = () => {
  const { topography, messages, currentTime, maxTime } = useGraphContext();

  return (
    <p>
      Nodes: {topography.nodes.size}<br/>
      Links: {topography.links.size}<br/>
      Fetched Messages: {messages.length}<br/>
      Current Time: {currentTime}<br/>
      Max Time: {maxTime}
    </p>
  );
}
