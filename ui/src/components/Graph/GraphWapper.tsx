"use client";

import { GraphContextProvider } from "@/contexts/GraphContext/GraphContextProvider";
import { FC } from "react";
import { Canvas } from "./modules/Canvas";
import { ChartTransactionsSent } from "./modules/Chart.TransactionsSent";
import { Controls } from "./modules/Controls";
import { Slider } from "./modules/Slider";
import { IServerNodeMap } from "./types";

export interface IGraphWrapperProps {
  topography: IServerNodeMap;
  maxTime: number;
}

export const GraphWrapper: FC<IGraphWrapperProps> = ({
  maxTime,
  topography,
}) => (
  <GraphContextProvider maxTime={maxTime} topography={topography}>
    <div className="container mx-auto">
      <div className="flex items-center justify-center gap-4 my-4 max-w-3xl mx-auto">
        <Slider />
        <Controls />
      </div>

      <div className="flex items-center justify-between gap-4">
        <Canvas />
        <div className="flex flex-col w-1/3 items-center justify-between gap-4">
          <div className="w-full h-[400px]">
            <ChartTransactionsSent />
          </div>
        </div>
      </div>
    </div>
  </GraphContextProvider>
);
