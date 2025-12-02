import {
  useSimContext,
  defaultAggregatedData,
} from "@/contexts/SimContext/context";
import { IScenario } from "@/contexts/SimContext/types";
import { ChangeEvent, FC, useCallback, useEffect, useState } from "react";
import { useStreamMessagesHandler } from "../hooks/useStreamMessagesHandler";
import { useLokiWebSocket } from "../hooks/useLokiWebSocket";
import { Button } from "@/components/Button";

export const Scenario: FC = () => {
  const {
    state: { allScenarios, activeScenario, events, lokiHost, lokiConnected },
    dispatch,
  } = useSimContext();
  const { startStream, streaming, stopStream } = useStreamMessagesHandler();
  const { connect: connectLoki, disconnect: disconnectLoki, connecting: lokiConnecting } = useLokiWebSocket();
  const [includeTransactions, setIncludeTransactions] = useState(true);

  const isLokiMode = !!lokiHost;

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
        trace: scenario.trace ? new URL(scenario.trace, window.location.toString()).toString() : undefined,
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
    if (isLokiMode) {
      disconnectLoki();
    } else {
      stopStream();
    }
    dispatch({ type: "RESET_TIMELINE" });
    dispatch({
      type: "BATCH_UPDATE",
      payload: {
        aggregatedData: defaultAggregatedData,
      },
    });
  }, [isLokiMode, disconnectLoki, stopStream, dispatch]);

  const handleStartStream = useCallback(() => {
    if (isLokiMode) {
      connectLoki();
    } else {
      startStream(includeTransactions);
    }
  }, [isLokiMode, connectLoki, startStream, includeTransactions]);

  const isLoaded = events.length > 0 || streaming || lokiConnected;
  const isConnecting = streaming || lokiConnecting;

  return (
    <div className="flex items-center justify-start gap-4 border-2 rounded-md p-4 border-gray-200 bg-white/80 backdrop-blur-xs">
      <div className="flex items-center gap-3">
        <label htmlFor="scenario" className="text-gray-900">
          Scenario
        </label>
        <select
          id="scenario"
          className="text-lg rounded-md font-medium transition-all duration-150 bg-transparent border border-gray-300 hover:border-gray-400 text-gray-900 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500 disabled:bg-gray-100 disabled:text-gray-500 disabled:border-gray-200 px-3 py-2 cursor-pointer disabled:cursor-not-allowed"
          value={activeScenario}
          onChange={chooseScenario}
        >
          {allScenarios.map((s) => (
            <option key={s.name}>{s.name}</option>
          ))}
        </select>
      </div>

      {!isLokiMode && (
        <div className="flex flex-col gap-1">
          <label className="flex items-center gap-2">
            <input
              type="checkbox"
              checked={includeTransactions}
              onChange={(e) => setIncludeTransactions(e.target.checked)}
              disabled={isConnecting || isLoaded}
            />
            Include Transactions
          </label>
        </div>
      )}

      <div className="flex gap-2">
        <Button
          variant="primary"
          onClick={handleStartStream}
          disabled={isConnecting || isLoaded}
        >
          {isLokiMode 
            ? (lokiConnecting ? "Connecting..." : lokiConnected ? "Connected" : "Connect") 
            : (streaming ? "Loading..." : isLoaded ? "Loaded" : "Load Scenario")
          }
        </Button>
        {isLoaded && (
          <Button
            variant="secondary"
            onClick={handleUnloadScenario}
            className="w-[80px]"
          >
            {isLokiMode 
              ? "Disconnect"
              : (streaming ? "Cancel" : "Reset")
            }
          </Button>
        )}
      </div>
    </div>
  );
};
