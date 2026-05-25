"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useEffect, useState } from "react";
import { parse } from "yaml";
import { Coord2D, Node } from "./topology";
import { GraphWrapper } from "../Graph/GraphWrapper";
import { ChainWrapper } from "../Chain/ChainWrapper";
import { Scenario } from "./modules/Scenario";
import { TimelineSlider } from "./modules/TimelineSlider";
import { Playback } from "./modules/Playback";
import { Stats } from "./modules/Stats";
import { LayoutSelector } from "./modules/LayoutSelector";
import { ITransformedNode } from "./types";
import { useGraphLayout } from "@/hooks/useGraphLayout";

type View = "network" | "chain";

const ViewToggle: FC<{ view: View; setView: (v: View) => void }> = ({
  view,
  setView,
}) => (
  <div className="flex items-center justify-start gap-3 border-2 rounded-md p-4 border-gray-200 bg-white/80 backdrop-blur-xs">
    <span className="text-gray-900">View</span>
    <div
      role="tablist"
      className="inline-flex rounded-md border border-gray-300 overflow-hidden"
    >
      {(["network", "chain"] as const).map((v) => (
        <button
          key={v}
          type="button"
          role="tab"
          aria-selected={view === v}
          onClick={() => setView(v)}
          className={`text-lg font-medium px-3 py-2 transition-colors duration-150 cursor-pointer focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500 ${
            view === v
              ? "bg-gray-800 text-white"
              : "bg-transparent text-gray-900 hover:bg-gray-100"
          }`}
        >
          {v === "network" ? "Network" : "Chain"}
        </button>
      ))}
    </div>
  </div>
);

export const SimWrapper: FC = () => {
  const {
    state: { topologyPath, topologyLoaded },
    dispatch,
  } = useSimContext();

  const [view, setView] = useState<View>("network");

  useGraphLayout();

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
      const links = new Map<
        string,
        {
          source: string;
          target: string;
          latencyMs?: number;
          bandwidthBytesPerSecond?: number;
        }
      >();
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
        // Extract producer relationships and latencies
        for (const [peerId, peerData] of Object.entries(node.producers)) {
          const linkIds = [id, peerId].sort();
          const linkKey = `${linkIds[0]}|${linkIds[1]}`;

          // Store latency and bandwidth from this node to the peer
          const latencyMs = (peerData as any)?.["latency-ms"];
          const bandwidthBytesPerSecond = (peerData as any)?.[
            "bandwidth-bytes-per-second"
          ];

          // Only set if we haven't seen this link before, or if this data is valid
          if (
            !links.has(linkKey) ||
            (latencyMs !== undefined && latencyMs !== null)
          ) {
            links.set(linkKey, {
              source: linkIds[0],
              target: linkIds[1],
              latencyMs: latencyMs,
              bandwidthBytesPerSecond: bandwidthBytesPerSecond,
            });
          }
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

  return (
    <div className="relative h-screen w-screen">
      <div className="flex flex-col items-start gap-4 z-10 absolute left-10 top-10 pointer-events-none">
        <div className="flex flex-row items-stretch gap-4 pointer-events-auto">
          <Scenario />
          <ViewToggle view={view} setView={setView} />
          {view === "network" ? <LayoutSelector /> : null}
        </div>
        <div className="pointer-events-auto"><Stats /></div>
      </div>
      {view === "network"
        ? topologyLoaded
          ? <GraphWrapper />
          : null
        : <ChainWrapper />}
      <div className="absolute bottom-10 left-10 right-10 z-10 border-2 rounded-md p-4 border-gray-200 bg-white/80 backdrop-blur-xs flex gap-4 pointer-events-auto">
        <Playback />
        <TimelineSlider />
      </div>
    </div>
  );
};
