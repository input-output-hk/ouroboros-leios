"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import { FC } from "react";
import { ChainCanvas } from "./modules/ChainCanvas";
import { ChainDetailsPanel } from "./modules/ChainDetailsPanel";

export const ChainWrapper: FC = () => {
  const {
    state: { selectedBlock },
  } = useSimContext();

  return (
    <div className="w-full h-full relative">
      <ChainCanvas />
      {selectedBlock ? (
        <div className="absolute right-10 top-32">
          <ChainDetailsPanel />
        </div>
      ) : null}
    </div>
  );
};
