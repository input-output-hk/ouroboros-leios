import oboe from "oboe";
import { Dispatch, SetStateAction } from "react";

import { EServerType, IServerMessage, ITransactionReceived, ITransformedNodeMap, TServerNodeMap } from "./types";

export const getSimulationTime = async (setMaxTime: Dispatch<SetStateAction<number>>) => {
  const url = new URL("/api/transactions/last", window.location.href);
  const time = fetch(url)
    .then(res => res.json())
    .then((data: IServerMessage<ITransactionReceived>) => {
      setMaxTime(data.time / 1_000_000);
    })
    
  return time;
}

export const streamMessages = async (
  setMessages: Dispatch<SetStateAction<IServerMessage[]>>,
  timestamp: number
) => {
  const url = new URL("/api/messages/batch", window.location.href);
  url.searchParams.set("time", timestamp.toString());

  const result: Set<IServerMessage> = new Set();
  let interval: Timer | null = null;
  let lastTimeStamp: number | null = null;
  
  oboe(url.toString())
    .node("!", function (msg: IServerMessage) {
      result.add(msg);
      
      // Debounce the state updates because we'll overload React if we don't.
      if (!interval) {
        interval = setTimeout(() => {
          setMessages([...result])
          if (lastTimeStamp !== null && timestamp !== lastTimeStamp) {
            this.abort();
          } else {
            interval = null;
            lastTimeStamp = timestamp;
          }
        }, 10)
      } else if (interval && timestamp !== lastTimeStamp) {
        this.abort();
      }
    })
};

export const streamTopography = (
  setNodeMap: Dispatch<SetStateAction<ITransformedNodeMap>>,
) => {
  oboe("/api/topography")
    .node("!", (res: TServerNodeMap) => {
      setNodeMap((prev) => {
        const newResult = {...prev};
        
        if (res.type === EServerType.NODE) {
          newResult.nodes.push({
            data: res.data,
            fx: res.data.location[0],
            fy: res.data.location[1],
            id: prev.nodes.length
          });
        } else {
          newResult.links.push({
            source: res.data.nodes[0],
            target: res.data.nodes[1]
          })
        }

        return newResult;
      });
    })
};
