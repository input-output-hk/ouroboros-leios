"use client";

import { MILLISECOND_RANGE } from "@/components/Graph/Graph";
import { streamMessages, streamTopography } from "@/components/Graph/queries";
import { IServerMessage, ITransformedNodeMap } from "@/components/Graph/types";
import { useEffect, useState } from "react";

export const Test = () => {
  const [nodes, setNodes] = useState<ITransformedNodeMap>({
    links: [],
    nodes: []
  });
  const [messages, setMessages] = useState<Set<IServerMessage>>(new Set());
  useEffect(() => {
    streamTopography(setNodes)
    streamMessages(setMessages, MILLISECOND_RANGE);
  }, [setNodes])

  return <>{nodes.nodes.length}, {nodes.links.length}, {messages.size}</>;
}
