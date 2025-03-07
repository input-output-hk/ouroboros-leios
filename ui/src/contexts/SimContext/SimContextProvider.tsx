"use client";
import {
  FC,
  PropsWithChildren,
  useMemo,
  useReducer,
  useRef
} from "react";

import { defaultState, SimContext } from "./context";
import { reducer } from "./reducer";

export const SimContextProvider: FC<PropsWithChildren> = ({ children }) => {
  const [state, dispatch] = useReducer(reducer, defaultState);

  // load topology
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
