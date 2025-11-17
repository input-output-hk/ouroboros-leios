import { FC, memo, useCallback } from "react";

import {
  defaultAggregatedData,
  useSimContext,
} from "@/contexts/SimContext/context";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const Controls: FC = memo(() => {
  const { state: { events }, dispatch } = useSimContext();
  const { startStream, streaming, stopStream } = useStreamMessagesHandler();

  const handleUnloadScenario = useCallback(() => {
    stopStream();
    dispatch({ type: "RESET_TIMELINE" });
    dispatch({
      type: "BATCH_UPDATE",
      payload: {
        aggregatedData: defaultAggregatedData,
      },
    });
  }, [stopStream, dispatch]);

  const isLoaded = events.length > 0 || streaming;

  return (
    <div className="min-w-[200px] flex items-center justify-end gap-4">
      <button
        className="bg-[blue] text-white rounded-md px-4 py-2"
        onClick={startStream}
        disabled={streaming || isLoaded}
      >
        {streaming ? "Loading..." : isLoaded ? "Loaded" : "Load Scenario"}
      </button>
      {isLoaded && (
        <button
          className="bg-gray-400 text-white w-[80px] rounded-md px-4 py-2"
          onClick={handleUnloadScenario}
        >
          {streaming ? "Cancel" : "Unload"}
        </button>
      )}
    </div>
  );
});
