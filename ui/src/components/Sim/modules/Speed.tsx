import { useSimContext } from "@/contexts/SimContext/context";
import { FC } from "react";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const Speed: FC = () => {
  const {
    state: { aggregated, batchSize, speedMultiplier },
    dispatch,
  } = useSimContext();
  const { streaming } = useStreamMessagesHandler();

  if (aggregated) {
    return (
      <div className="min-w-32">
        <label htmlFor="speedMultiplier" className="block text-xs text-gray-600">
          Speed
        </label>
        <select name="speedMultiplier" className="mt-1 w-full text-lg" disabled={streaming} value={speedMultiplier} onChange={(e) => {
          dispatch({
            type: "SET_SPEED", payload: {
              batchSize,
              speedMultiplier: Number(e.target.value),
            }
          })
        }}>
          <option value={1}>1x</option>
          <option value={10}>10x</option>
          <option value={100}>100x</option>
        </select>
      </div>
    );
  } else {
    return (
      <div className="min-w-32">
        <label htmlFor="batchSize" className="block text-xs text-gray-600">
          Batch Size
        </label>
        <input
          name="batchSize"
          className="appearance-none outline-0 text-lg w-full"
          disabled={streaming}
          type="number"
          value={batchSize}
          onChange={(e) =>
            dispatch({
              type: "SET_SPEED", payload: {
                batchSize: Number(e.target.value),
                speedMultiplier,
              }
            })
          }
        />
      </div>
    );

  }
};
