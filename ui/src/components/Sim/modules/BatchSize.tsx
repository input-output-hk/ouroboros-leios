import { useSimContext } from "@/contexts/SimContext/context";
import { FC } from "react";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const BatchSize: FC = () => {
  const {
    state: { batchSize },
    dispatch,
  } = useSimContext();
  const { streaming } = useStreamMessagesHandler();

  return (
    <div className="-mb-1">
      <label htmlFor="batchSize" className="block text-xs text-gray-600">
        Batch Size
      </label>
      <input
        id="batchSize"
        className="appearance-none outline-0 text-lg"
        disabled={streaming}
        type="number"
        value={batchSize}
        onChange={(e) =>
          dispatch({ type: "SET_BATCH_SIZE", payload: Number(e.target.value) })
        }
      />
    </div>
  );
};
