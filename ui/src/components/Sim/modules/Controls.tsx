import { FC, memo, useCallback, useState } from "react";

import {
  defaultAggregatedData,
  useSimContext,
} from "@/contexts/SimContext/context";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const Controls: FC = memo(() => {
  const { state: { events }, dispatch } = useSimContext();
  const { startStream, streaming, stopStream } = useStreamMessagesHandler();
  const [includeTransactions, setIncludeTransactions] = useState(false);

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

  const handleStartStream = useCallback(() => {
    startStream(includeTransactions);
  }, [startStream, includeTransactions]);

  const isLoaded = events.length > 0 || streaming;

  return (
    <div className="min-w-[200px] flex items-center justify-end gap-4">
      <div className="flex flex-col gap-1">
        <label className="flex items-center gap-2 text-sm">
          <input
            type="checkbox"
            checked={includeTransactions}
            onChange={(e) => setIncludeTransactions(e.target.checked)}
            disabled={streaming || isLoaded}
          />
          Include Transactions
        </label>
      </div>
      <button
        className="bg-[blue] text-white rounded-md px-4 py-2"
        onClick={handleStartStream}
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
