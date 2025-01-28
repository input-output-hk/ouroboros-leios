"use client";

import { FC } from "react";
import { Canvas } from "./modules/Canvas";
import { NodeStats } from "./modules/NodeStats";

export const GraphWrapper: FC = ({ }) => {
  return (
    <div className="w-full h-full relative">
      <Canvas />
      <NodeStats />
    </div>
  );
};
