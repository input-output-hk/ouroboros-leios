"use client";

import { SimContextProvider } from "@/contexts/SimContext/SimContextProvider";
import { FC, useState } from "react";
import { BlocksView } from "../Blocks/BlocksView";
import { GraphWrapper } from "../Graph/GraphWrapper";
import { BatchSize } from "./modules/BatchSize";
import { Controls } from "./modules/Controls";
import { Progress } from "./modules/Slider";
import { Stats } from "./modules/Stats";
import { IServerNodeMap } from "./types";

export interface ISimWrapperProps {
  topography: IServerNodeMap;
  maxTime: number;
}

enum Tab {
  Graph,
  Blocks,
}

interface ITabButtonProps {
  name: string;
  active: boolean;
  onClick: () => void;
}

const TabButton: FC<ITabButtonProps> = ({ name, active, onClick }) => {
  const color = active ? "bg-[blue]" : "bg-gray-400";
  return <button className={`${color} text-white rounded-md px-4 py-2`} onClick={onClick}>{name}</button>
}

export const SimWrapper: FC<ISimWrapperProps> = ({
  maxTime,
  topography,
}) => {
  const [activeTab, setActiveTab] = useState(Tab.Graph);
  return (
    <SimContextProvider maxTime={maxTime} topography={topography}>
      <div className="flex flex-col items-center justify-between gap-4 z-10 absolute left-10 top-10">
        <Stats />
      </div>
      <div className="flex items-center justify-between gap-4 relative h-screen w-screen">
        {activeTab == Tab.Graph ? <GraphWrapper /> : null}
        {activeTab == Tab.Blocks ? <BlocksView /> : null}
        <div className="absolute top-10 w-full">
          <div className="flex justify-center gap-4 min-w-[200px]">
            <TabButton name="Graph" active={activeTab == Tab.Graph} onClick={() => setActiveTab(Tab.Graph)} />
            <TabButton name="Blocks" active={activeTab == Tab.Blocks} onClick={() => setActiveTab(Tab.Blocks)} />
          </div>
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
    </SimContextProvider>
  );
};