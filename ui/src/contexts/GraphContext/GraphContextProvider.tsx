"use client";
import {
  FC,
  PropsWithChildren,
  useMemo,
  useReducer,
  useRef
} from "react";

import { IGraphWrapperProps } from "@/components/Graph/GraphWapper";
import {
  ITransformedNodeMap
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
          `node-${i}`,
          {
            data: n,
            fy: n.location[0],
            fx: n.location[1],
            id: `node-${i}`,
          },
        ]),
      ),
      links: new Map(
        topography.links.map((l) => [
          `${l.nodes[0]}|${l.nodes[1]}`,
          {
            source: `node-${l.nodes[0]}`,
            target: `node-${l.nodes[1]}`,
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
  const resolvedState = useMemo(
    () => ({
      ...state,
      canvasRef,
    }),
    [state],
  );

  return (
    <GraphContext.Provider value={{ state: resolvedState, dispatch }}>
      {children}
    </GraphContext.Provider>
  );
};
