import { useSimContext } from "@/contexts/SimContext/context";
import { IScenario } from "@/contexts/SimContext/types";
import { ChangeEvent, FC, useCallback, useEffect } from "react";

export const Scenario: FC = () => {
  const { state: {
    allScenarios,
    activeScenario,
  }, dispatch } = useSimContext();

  useEffect(() => {
    (async () => {
      const response = await fetch("scenarios.json");
      const { scenarios }: { scenarios: IScenario[] } = await response.json();
      dispatch({ type: "SET_SCENARIOS", payload: scenarios });
    })();
  }, []);

  const chooseScenario = useCallback((event: ChangeEvent<HTMLSelectElement>) => {
    dispatch({ type: "SET_SCENARIO", payload: event.target.value });
  }, [allScenarios]);

  return (
    <div className="min-w-32">
      <label htmlFor="scenario" className="block text-xs text-gray-600">
        Scenario
      </label>
      <select id="scenario" className="mt-1 w-full text-lg"
        value={activeScenario} onChange={chooseScenario}>
        {allScenarios.map(s => <option key={s.name}>{s.name}</option>)}
      </select>
    </div>
  );
}