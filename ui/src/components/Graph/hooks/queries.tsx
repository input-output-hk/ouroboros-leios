import oboe, { Oboe } from "oboe";
import { useCallback, useEffect, useRef } from "react";

import { IGraphContextState } from "@/contexts/GraphContext/types";
import { ILink, INode, IServerMessage, ITransactionReceived, ITransformedNodeMap } from "../types";

export const useSetSimulationTimeHandler = ({ setMaxTime }: IGraphContextState) => {
  const handleRequest = useCallback(() => {
    const url = new URL("/api/transactions/last", window.location.href);
    const time = fetch(url)
      .then(res => res.json())
      .then((data: IServerMessage<ITransactionReceived>) => {
        setMaxTime(data.time / 1_000_000);
      })

    return time;
  }, [])
    
  return handleRequest;
}

export const useStreamMessagesHandler = ({ setMessages, messages, currentTime }: IGraphContextState) => {
  const debounceTimeoutRef = useRef<Timer | null>(null);
  const isAborted = useRef<boolean>(false);
  const oboeInstance = useRef<Oboe>();

  const handleRequest = useCallback(() => {
    const url = new URL("/api/messages/batch", window.location.href);
    url.searchParams.set("time", currentTime.toString());
    const result: Set<IServerMessage> = new Set();
  
    oboeInstance.current = oboe(url.toString())
      .node("!", function (msg: IServerMessage) {
        if (isAborted.current) {
          // @ts-expect-error
          this.abort(); // Safely abort if marked as aborted
          return;
        }
  
        result.add(msg);
  
        // Debounce state updates
        if (!debounceTimeoutRef.current) {
          debounceTimeoutRef.current = setTimeout(() => {
            setMessages([...result]);
            debounceTimeoutRef.current = null; // Clear the interval after the update
          }, 50);
        }
      });
  }, [currentTime])

  useEffect(() => {
    // Abort logic when `timestamp` changes
    return () => {
      if (debounceTimeoutRef.current) {
        clearTimeout(debounceTimeoutRef.current);
        debounceTimeoutRef.current = null;
      }
      isAborted.current = true; // Mark as aborted
      if (oboeInstance.current) {
        oboeInstance.current.abort(); // Abort the oboe instance
      }
    };
  }, [])

  return handleRequest;
};

export const useSetTopographyHandler = ({ setTopography, setTopographyLoaded }: IGraphContextState) => {
  const handleRequest = useCallback(() => {
    fetch("/api/topography")
      .then(res => res.json())
      .then((data: { links: ILink[]; nodes: INode[] }) => {
        const newResult: ITransformedNodeMap = {
          nodes: new Map(data.nodes.map((n, i) => [
            i,
            {
              data: n,
              fx: n.location[0],
              fy: n.location[1],
              id: i
            }
          ])),
          links: new Map(data.links.map(l => [
            `${l.nodes[0]}|${l.nodes[1]}`,
              {
              source: l.nodes[0],
              target: l.nodes[1]
            }
          ]))
        }
  
        setTopography(newResult);
      })
      .then(() => setTopographyLoaded(true))
  }, [])

  return handleRequest;
};
