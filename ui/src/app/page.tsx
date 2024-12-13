import { GraphWrapper } from "@/components/Graph/GraphWapper";
import { getSetSimulationMaxTime, getSimulationTopography } from "./queries";

export default async function Home() {
  const [maxTime, topography] = await Promise.all([
    getSetSimulationMaxTime(),
    getSimulationTopography(),
  ]);

  return (
    <div>
      <main className="flex flex-col gap-8 row-start-2 items-center sm:items-start overflow-hidden">
        <GraphWrapper maxTime={maxTime} topography={topography}/>
      </main>
    </div>
  );
}
