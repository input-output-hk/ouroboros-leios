"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useEffect } from "react";
import { parse } from "yaml";
import { Coord2D, Node } from "../../../../data/simulation/topology";
import { GraphWrapper } from "../Graph/GraphWrapper";
import { Scenario } from "./modules/Scenario";
import { TimelineSlider } from "./modules/TimelineSlider";
import { Playback } from "./modules/Playback";
import { Stats } from "./modules/Stats";
import { ITransformedNode } from "./types";


export const SimWrapper: FC = () => {
  const {
    state: {
      topologyPath,
      topologyLoaded,
    },
    dispatch,
  } = useSimContext();

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
      const links = new Map<string, { source: string; target: string; latencyMs?: number }>();
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
          
          // Store latency from this node to the peer
          const latencyMs = (peerData as any)?.['latency-ms'];
          
          // Only set latency if we haven't seen this link before, or if this latency is valid
          if (!links.has(linkKey) || (latencyMs !== undefined && latencyMs !== null)) {
            links.set(linkKey, {
              source: linkIds[0],
              target: linkIds[1],
              latencyMs: latencyMs,
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
    <>
      <div className="flex flex-col items-center justify-between gap-4 z-10 absolute left-10 top-10">
        <Stats />
      </div>
      <div className="flex items-center justify-center gap-4 relative h-screen w-screen">
        {topologyLoaded ? <GraphWrapper /> : null}
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
