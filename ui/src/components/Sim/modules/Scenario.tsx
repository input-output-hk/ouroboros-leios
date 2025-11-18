import {
  useSimContext,
  defaultAggregatedData,
} from "@/contexts/SimContext/context";
import { IScenario } from "@/contexts/SimContext/types";
import { ChangeEvent, FC, useCallback, useEffect, useState } from "react";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";

export const Scenario: FC = () => {
  const {
    state: { allScenarios, activeScenario, events },
    dispatch,
  } = useSimContext();
  const { startStream, streaming, stopStream } = useStreamMessagesHandler();
  const [includeTransactions, setIncludeTransactions] = useState(false);

  useEffect(() => {
    (async () => {
      const response = await fetch("scenarios.json");
      const body: { scenarios: IScenario[] } = await response.json();
      const scenarios = body.scenarios.map((scenario) => ({
        ...scenario,
        topology: new URL(
          scenario.topology,
          window.location.toString(),
        ).toString(),
        trace: new URL(scenario.trace, window.location.toString()).toString(),
      }));
      dispatch({ type: "SET_SCENARIOS", payload: scenarios });
    })();
  }, []);

  const chooseScenario = useCallback(
    (event: ChangeEvent<HTMLSelectElement>) => {
      dispatch({ type: "SET_SCENARIO", payload: event.target.value });
    },
    [allScenarios],
  );

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
    <div className="flex items-center justify-start gap-4">
      <div className="min-w-32">
        <label htmlFor="scenario" className="block text-xs text-gray-600">
          Scenario
        </label>
        <select
          id="scenario"
          className="mt-1 w-full text-lg"
          value={activeScenario}
          onChange={chooseScenario}
        >
          {allScenarios.map((s) => (
            <option key={s.name}>{s.name}</option>
          ))}
        </select>
      </div>

      <div className="flex gap-2">
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
    </div>
  );
};
