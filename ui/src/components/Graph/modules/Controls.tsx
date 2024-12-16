import { FC, memo } from "react";

import { useHandlers } from "../hooks/useHandlers";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const Controls: FC = memo(() => {
  const { handleResetSim } = useHandlers();
  const { startStream, streaming } = useStreamMessagesHandler();

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
        disabled={streaming}
        className="bg-gray-400 text-white w-[80px] rounded-md px-4 py-2"
        onClick={handleResetSim}
      >
        Reset
      </button>
    </div>
  );
});
