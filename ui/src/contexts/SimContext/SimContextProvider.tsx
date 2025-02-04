"use client";
import {
  FC,
  PropsWithChildren,
  useMemo,
  useReducer,
  useRef
} from "react";

import {
  IServerNodeMap,
  ITransformedNodeMap
} from "@/components/Sim/types";
import { defaultState, SimContext } from "./context";
import { reducer } from "./reducer";

export interface ISimContextProviderProps {
  topography: IServerNodeMap;
  maxTime: number;
}

export const SimContextProvider: FC<
  PropsWithChildren<ISimContextProviderProps>
> = ({ children, topography, maxTime }) => {
  const defaultSyncedState = useMemo(() => {
    const transformedTopography: ITransformedNodeMap = {
      nodes: new Map(
        topography.nodes.map((n) => [
          n.id,
          {
            data: n,
            fy: n.location[0],
            fx: n.location[1],
            id: n.id,
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

  const canvasRef = useRef<HTMLCanvasElement>(defaultState.graph.canvasRef.current);
  const resolvedState = useMemo(
    () => ({
      ...state,
      graph: {
        ...state.graph,
        canvasRef,
      }
    }),
    [state],
  );

  return (
    <SimContext.Provider value={{ state: resolvedState, dispatch }}>
      {children}
    </SimContext.Provider>
  );
};
