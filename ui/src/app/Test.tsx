"use client";

import { useGraphContext } from "@/contexts/GraphContext/context";

export const Test = () => {
  const { topography, messages, currentTime, maxTime } = useGraphContext();

  console.log(messages[messages.length -1]?.time)

  return (
    <p>
      Nodes: {topography.nodes.length}<br/>
      Links: {topography.links.length}<br/>
      Fetched Messages: {messages.length}<br/>
      Current Time: {currentTime}<br/>
      Max Time: {maxTime}
    </p>
  );
}
