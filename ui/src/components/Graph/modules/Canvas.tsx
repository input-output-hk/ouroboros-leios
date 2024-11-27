"use client";

import { useGraphContext } from "@/contexts/GraphContext/context";
import { FC, useEffect } from "react";
import { useHandlers } from "../hooks/useHandlers";

export const Canvas: FC = () => {
  const { state: { sentTxs, generatedMessages, canvasRef } } = useGraphContext();
  const { drawCanvas } = useHandlers();

  useEffect(() => {
    drawCanvas();
  }, [])

  return (
    <div className="h-[80vh] border-2 border-gray-200 rounded mb-8 w-2/3">
      <div className="flex items-center justify-center gap-4 mt-4">
        <div>
          <h4>Transactions Generated: {generatedMessages.length}</h4>
        </div>
        <div>
          <h4>Propagations: {sentTxs.length}</h4>
        </div>
      </div>
      <canvas ref={canvasRef} />
    </div>
  )
}
