import { FC, memo } from "react";

import { useHandlers } from "../hooks/useHandlers";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const Controls: FC = memo(() => {
  const { handleResetSim } = useHandlers();
  const { startStream, streaming } = useStreamMessagesHandler();

  return (
    <>
      <button
        className="bg-blue-500 text-white rounded-md px-4 py-2"
        onClick={startStream}
        disabled={streaming}
      >
        {streaming ? "Aggregating..." : "Aggregate"}
      </button>
      <button
        disabled={streaming}
        className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
        onClick={handleResetSim}
      >
        Reset
      </button>
    </>
  );
});
