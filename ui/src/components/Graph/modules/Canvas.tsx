"use client";

import { useGraphContext } from "@/contexts/GraphContext/context";
import debounce from "debounce";
import { FC, useEffect } from "react";
import { useHandlers } from "../hooks/useHandlers";
import { isClickOnNode } from "../utils";

export const Canvas: FC = () => {
  const {
    state: { canvasRef, topography, currentNode },
    dispatch,
  } = useGraphContext();
  const { drawTopography } = useHandlers();

  useEffect(() => {
    drawTopography();
    canvasRef.current?.addEventListener("click", (ev) => {
      if (!canvasRef.current) {
        return;
      }

      const width =
        canvasRef.current.parentElement?.getBoundingClientRect().width || 1024;
      const height =
        canvasRef.current.parentElement?.getBoundingClientRect().height || 800;
      const rect = canvasRef.current.getBoundingClientRect();
      const x = ev.clientX - rect.left;
      const y = ev.clientY - rect.top;
      const { node } = isClickOnNode(
        x,
        y,
        topography,
        width,
        height,
        2,
      );

      dispatch({ type: "SET_CURRENT_NODE", payload: node });
    });

    const redraw = debounce(drawTopography, 100);

    window.addEventListener("resize", redraw)

    return () => window.removeEventListener("resize", redraw)
  }, []);

  useEffect(drawTopography, [currentNode]);

  return (
    <div className="h-[80vh] border-2 border-gray-200 rounded mb-8 w-2/3">
      <canvas ref={canvasRef} />
    </div>
  );
};
