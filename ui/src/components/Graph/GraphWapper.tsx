"use client";

import { GraphContextProvider } from "@/contexts/GraphContext/GraphContextProvider";
import { FC } from "react";
import { BatchSize } from "./modules/BatchSize";
import { Canvas } from "./modules/Canvas";
import { Controls } from "./modules/Controls";
import { NodeStats } from "./modules/NodeStats";
import { Progress } from "./modules/Slider";
import { Stats } from "./modules/Stats";
import { IServerNodeMap } from "./types";

export interface IGraphWrapperProps {
  topography: IServerNodeMap;
  maxTime: number;
}

export const GraphWrapper: FC<IGraphWrapperProps> = ({
  maxTime,
  topography,
}) => {
  return (
    <GraphContextProvider maxTime={maxTime} topography={topography}>
      <div className="flex flex-col items-center justify-between gap-4 z-10 absolute left-10 top-10">
        <Stats />
      </div>
      <div className="flex items-center justify-between gap-4 relative h-screen w-screen">
        <div className="w-full h-full relative">
          <Canvas />
          <NodeStats />
        </div>
        <div className="absolute bottom-12 w-full">
          <div className="flex border-2 rounded-md p-4 border-gray-200 items-end justify-center gap-4 my-4 max-w-3xl mx-auto bg-white/80 backdrop-blur-sm">
            <Controls />
            <Progress />
          </div>
          <div className="flex items-end justify-center gap-4 my-4 max-w-sm mx-auto bg-white/80 backdrop-blur-sm">
            <BatchSize />
          </div>
        </div>
      </div>
    </GraphContextProvider>
  );
};
