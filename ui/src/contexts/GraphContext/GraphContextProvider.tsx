"use client";
import {
  FC,
  PropsWithChildren,
  useCallback,
  useEffect,
  useMemo,
  useReducer,
  useRef,
} from "react";

import { IGraphWrapperProps } from "@/components/Graph/GraphWapper";
import {
  IServerMessage,
  ITransactionGenerated,
  ITransactionMessage,
  ITransactionReceived,
  ITransactionSent,
  ITransformedNodeMap,
} from "@/components/Graph/types";
import { defaultState, GraphContext } from "./context";
import { reducer } from "./reducer";

export const GraphContextProvider: FC<
  PropsWithChildren<IGraphWrapperProps>
> = ({ children, topography, maxTime }) => {
  const defaultSyncedState = useMemo(() => {
    const transformedTopography: ITransformedNodeMap = {
      nodes: new Map(
        topography.nodes.map((n, i) => [
          i,
          {
            data: n,
            fx: n.location[0],
            fy: n.location[1],
            id: i,
          },
        ]),
      ),
      links: new Map(
        topography.links.map((l) => [
          `${l.nodes[0]}|${l.nodes[1]}`,
          {
            source: l.nodes[0],
            target: l.nodes[1],
          },
        ]),
      ),
    };

    return {
      ...defaultState,
      maxTime,
      topography: transformedTopography,
      topographyLoaded: true,
    };
  }, []);

  const [state, dispatch] = useReducer(reducer, defaultSyncedState);

  const canvasRef = useRef<HTMLCanvasElement>(defaultState.canvasRef.current);
  const intervalId = useRef<number | null>(defaultState.intervalId.current);
  const simulationPauseTime = useRef<number>(
    defaultState.simulationPauseTime.current,
  );
  const simulationStartTime = useRef<number>(
    defaultState.simulationStartTime.current,
  );

  // Mutable refs to store messages and transactions without causing re-renders
  const transactionsByIdRef = useRef<Map<number, ITransactionMessage[]>>(
    new Map(),
  );
  const txGeneratedMessagesById = useRef<
    Map<number, IServerMessage<ITransactionGenerated>>
  >(new Map());
  const txSentMessagesById = useRef<
    Map<number, IServerMessage<ITransactionSent>[]>
  >(new Map());
  const txReceivedMessagesById = useRef<
    Map<number, IServerMessage<ITransactionReceived>[]>
  >(new Map());

  const resolvedState = useMemo(
    () => ({
      ...state,
      canvasRef,
      transactionsByIdRef,
      txGeneratedMessagesById,
      txSentMessagesById,
      txReceivedMessagesById,
      intervalId,
      simulationPauseTime,
      simulationStartTime,
    }),
    [state],
  );

  const aggregateSimluationData = useCallback(() => {
    const now = performance.now();
    const elapsed =
      simulationStartTime.current !== 0
        ? (now - simulationStartTime.current) * state.speed
        : 0;

    // Aggregate total propagated transactions at current time.
    const sentTxs: number[] = [];
    for (const txList of transactionsByIdRef.current.values()) {
      for (const { duration, sentTime } of txList) {
        if (elapsed > sentTime + duration) {
          sentTxs.push(sentTime);
        }
      }
    }

    // Aggregate generated transactions.
    const generatedMessages: number[] = [];
    defaultSyncedState.topography.nodes.forEach((node) => {
      txGeneratedMessagesById.current.forEach((m) => {
        const target = m.time / 1_000_000;

        if (m.message.publisher === node.id && elapsed > target) {
          generatedMessages.push(m.time / 1_000_000);
        }
      });
    });

    dispatch({
      type: "BATCH_UPDATE",
      payload: {
        sentTxs,
        generatedMessages,
      },
    });
  }, [state.speed, defaultSyncedState.topography.nodes]);

  useEffect(() => {
    let interval: Timer | undefined = undefined;
    if (state.playing) {
      interval = setInterval(aggregateSimluationData, 10000 * state.speed);
    } else if (interval !== undefined) {
      clearInterval(interval);
    }

    return () => {
      clearInterval(interval);
    };
  }, [state.playing, state.speed]);

  return (
    <GraphContext.Provider value={{ state: resolvedState, dispatch }}>
      {children}
    </GraphContext.Provider>
  );
};
