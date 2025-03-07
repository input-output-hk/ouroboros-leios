"use client";

import { SimWrapper } from "@/components/Sim/SimWrapper";
import { SimContextProvider } from "@/contexts/SimContext/SimContextProvider";

export default function Home() {
  return (
    <main className="flex flex-col">
      <SimContextProvider>
        <SimWrapper />
      </SimContextProvider>
    </main>
  );
}