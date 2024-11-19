import { FC, PropsWithChildren, useEffect, useMemo, useRef, useState } from "react";

import { getSimulationTime, streamMessages, streamTopography } from "@/components/Graph/queries";
import { IServerMessage, ITransactionMessage, ITransformedNodeMap } from "@/components/Graph/types";
import { GraphContext } from "./context";
import { ESpeedOptions, IGraphContextState } from "./types";

export const GraphContextProvider: FC<PropsWithChildren> = ({ children }) => {
  const [currentTime, setCurrentTime] = useState(0);
  const intervalId = useRef<Timer | null>(null);
  const [maxTime, setMaxTime] = useState(0);
  const [messages, setMessages] = useState<IServerMessage[]>([]);
  const [playing, setPlaying] = useState(false);
  const [sentTxs, setSentTxs] = useState<Set<string>>(new Set());
  const simulationPauseTime = useRef<number>(0);
  const simulationStartTime = useRef<number>(0);
  const [speed, setSpeed] = useState(ESpeedOptions["3/10"]);
  const [topography, setTopography] = useState<ITransformedNodeMap>({ links: [], nodes: [] });
  const [transactions, setTransactions] = useState<Map<number, ITransactionMessage[]>>(new Map());

  const fetchingMessages = useRef(false);

  const state: IGraphContextState = useMemo(() => {
    return {
      currentTime,
      intervalId,
      maxTime,
      messages,
      playing,
      sentTxs,
      simulationPauseTime,
      simulationStartTime,
      speed,
      topography,
      transactions,
      setCurrentTime,
      setPlaying,
      setSentTxs,
      setSpeed,
      setMaxTime,
      setMessages,
      setTopography,
      setTransactions
    }
  }, [topography, speed, sentTxs, messages, maxTime, playing, transactions, currentTime])

  useEffect(() => {
    streamTopography(setTopography)
    getSimulationTime(setMaxTime);
  }, [])

  // Update to update on currentTime change
  useEffect(() => {
    streamMessages(setMessages, currentTime)
  }, [currentTime])

  return (
    <GraphContext.Provider value={state}>
      {children}
    </GraphContext.Provider>
  )
}
