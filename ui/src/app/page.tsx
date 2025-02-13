import { SimWrapper } from "@/components/Sim/SimWrapper";
import { SimContextProvider } from "@/contexts/SimContext/SimContextProvider";
import { getSimulationMaxTime, getSimulationTopography } from "./queries";

export default async function Home() {
  const [maxTime, topography] = await Promise.all([
    getSimulationMaxTime(),
    getSimulationTopography(),
  ]);

  return (
    <div>
      <main className="flex flex-col gap-8 row-start-2 items-center sm:items-start overflow-hidden">
        <SimContextProvider maxTime={maxTime} topography={topography}>
          <SimWrapper />
        </SimContextProvider>
      </main>
    </div>
  );
}
