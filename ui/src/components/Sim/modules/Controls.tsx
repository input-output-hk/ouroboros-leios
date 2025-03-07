import { FC, memo, useCallback } from "react";

import { defaultAggregatedData, useSimContext } from "@/contexts/SimContext/context";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const Controls: FC = memo(() => {
  const { state, dispatch } = useSimContext();
  const { startStream, streaming, stopStream } = useStreamMessagesHandler();

  const handleCancelSim = useCallback(() => {
    stopStream();
    dispatch({
      type: "BATCH_UPDATE",
      payload: {
        graph: {
          ...state.graph,
          currentNode: undefined,
        },
        blocks: {
          ...state.blocks,
          currentBlock: undefined,
        },
        aggregatedData: defaultAggregatedData,
      },
    });
  }, [stopStream, state, dispatch])

  return (
    <div className="min-w-[200px] flex items-center justify-end gap-4">
      <button
        className="bg-[blue] text-white rounded-md px-4 py-2"
        onClick={startStream}
        disabled={streaming}
      >
        {streaming ? "Running..." : "Run Sim"}
      </button>
      <button
        className="bg-gray-400 text-white w-[80px] rounded-md px-4 py-2"
        onClick={handleCancelSim}
      >
        {streaming ? "Cancel" : "Reset"}
      </button>
    </div>
  );
});
