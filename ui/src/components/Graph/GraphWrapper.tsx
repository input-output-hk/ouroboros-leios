"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import { FC } from "react";
import { Canvas } from "./modules/Canvas";
import { NodeStats } from "./modules/NodeStats";

export const GraphWrapper: FC = ({}) => {
  const {
    state: {
      graph: { currentNode },
    },
  } = useSimContext();
  return (
    <div className="w-full h-full relative">
      <Canvas />
      {currentNode ? (
        <div className="absolute right-10 top-10">
          <NodeStats />
        </div>
      ) : null}
    </div>
  );
};
