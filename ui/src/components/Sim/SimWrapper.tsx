"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import { Tab } from "@/contexts/SimContext/types";
import { FC, useCallback, useEffect } from "react";
import { parse } from "yaml";
import { Coord2D, Node } from "../../../../data/simulation/topology";
import { useTimelinePlayback } from "@/hooks/useTimelinePlayback";
import { BlocksView } from "../Blocks/BlocksView";
import { GraphWrapper } from "../Graph/GraphWrapper";
import { TransactionsView } from "../Transactions/TransactionsView";
import { Scenario } from "./modules/Scenario";
import { TimelineSlider } from "./modules/TimelineSlider";
import { Playback } from "./modules/Playback";
import { Stats } from "./modules/Stats";
import { ITransformedNode } from "./types";

interface ITabButtonProps {
  name: string;
  active: boolean;
  onClick: () => void;
}

const TabButton: FC<ITabButtonProps> = ({ name, active, onClick }) => {
  const color = active ? "bg-[blue]" : "bg-gray-400";
  return (
    <button
      className={`${color} text-white rounded-md px-4 py-2`}
      onClick={onClick}
    >
      {name}
    </button>
  );
};

export const SimWrapper: FC = ({}) => {
  const {
    state: {
      activeTab,
      topologyPath,
      topologyLoaded,
      blocks: { currentBlock },
    },
    dispatch,
  } = useSimContext();

  // Enable timeline playback
  useTimelinePlayback();

  // Load topology if it has changed
  useEffect(() => {
    dispatch({ type: "RESET_TOPOLOGY", payload: topologyPath });
    if (!topologyPath) {
      return;
    }
    (async () => {
      const topographyRes = await fetch(topologyPath);
      const topography = parse(await topographyRes.text());
      const nodes = new Map<string, ITransformedNode>();
      const links = new Map<string, { source: string; target: string }>();
      for (const [id, node] of Object.entries<Node<Coord2D>>(
        topography.nodes,
      )) {
        nodes.set(id, {
          data: {
            location: node.location,
            stake: node.stake as unknown as number,
          },
          fy: node.location[0],
          fx: node.location[1],
          id,
        });
        for (const peerId of Object.keys(node.producers)) {
          const linkIds = [id, peerId].sort();
          links.set(`${linkIds[0]}|${linkIds[1]}`, {
            source: linkIds[0],
            target: linkIds[1],
          });
        }
      }
      dispatch({
        type: "SET_TOPOLOGY",
        payload: {
          topologyPath,
          topology: { nodes, links },
        },
      });
    })();
  }, [topologyPath]);

  const setActiveTab = useCallback(
    (tab: Tab) => dispatch({ type: "SET_ACTIVE_TAB", payload: tab }),
    [dispatch],
  );
  return (
    <>
      {activeTab === Tab.Graph ? (
        <div className="flex flex-col items-center justify-between gap-4 z-10 absolute left-10 top-10">
          <Stats />
        </div>
      ) : null}
      <div className="flex items-center justify-center gap-4 relative h-screen w-screen">
        {activeTab === Tab.Graph && topologyLoaded ? <GraphWrapper /> : null}
        {activeTab === Tab.Blocks ? <BlocksView /> : null}
        {activeTab === Tab.Transactions ? <TransactionsView /> : null}
        <div className="absolute top-10 w-full">
          <div className="flex justify-center gap-4 min-w-[200px]">
            <TabButton
              name="Graph"
              active={activeTab === Tab.Graph}
              onClick={() => setActiveTab(Tab.Graph)}
            />
            <TabButton
              name="Blocks"
              active={activeTab === Tab.Blocks && currentBlock === undefined}
              onClick={() => setActiveTab(Tab.Blocks)}
            />
            <TabButton
              name="Transactions"
              active={activeTab === Tab.Transactions}
              onClick={() => setActiveTab(Tab.Transactions)}
            />
          </div>
        </div>
        <div className="absolute bottom-12 flex w-3/4 gap-4 justify-center">
          <div className="flex flex-shrink-0 border-2 rounded-md p-4 border-gray-200 gap-4 my-4 mx-auto bg-white/80 backdrop-blur-xs">
            <Scenario />
          </div>
          <div className="flex border-2 rounded-md p-4 border-gray-200 gap-4 my-4 mx-auto w-full bg-white/80 backdrop-blur-xs">
            <Playback />
            <TimelineSlider />
          </div>
        </div>
      </div>
    </>
  );
};
