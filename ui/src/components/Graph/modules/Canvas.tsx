"use client";

import { useGraphContext } from "@/contexts/GraphContext/context";
import debounce from "debounce";
import { FC, useEffect } from "react";
import { useHandlers } from "../hooks/useHandlers";
import { getOffsetCoordinates, isClickOnNode } from "../utils";

export const Canvas: FC = () => {
  const {
    state: {
      canvasRef,
      canvasOffsetX,
      canvasOffsetY,
      canvasScale,
      topography,
      currentNode,
    },
    dispatch,
  } = useGraphContext();
  const { drawTopography } = useHandlers();

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) {
      return;
    }

    const width = canvas.parentElement?.getBoundingClientRect().width || 1024;
    const height = canvas.parentElement?.getBoundingClientRect().height || 800;
    const { offsetX, offsetY } = getOffsetCoordinates(topography, width, height, canvasScale)
    dispatch({
      type: "SET_CANVAS_PROPS",
      payload: {
        canvasOffsetX: offsetX,
        canvasOffsetY: offsetY
      }
    })
  }, [])

  useEffect(() => {
    drawTopography();
    const canvas = canvasRef.current;
    if (!canvas) {
      return;
    }

    canvas.addEventListener("click", (ev) => {
      const width = canvas.parentElement?.getBoundingClientRect().width || 1024;
      const height =
        canvas.parentElement?.getBoundingClientRect().height || 800;
      const rect = canvas.getBoundingClientRect();
      const x = ev.clientX - rect.left;
      const y = ev.clientY - rect.top;
      const { node } = isClickOnNode(x, y, topography, width, height, 2, canvasScale);

      dispatch({ type: "SET_CURRENT_NODE", payload: node });
    });

    const handleWheel = (event: WheelEvent) => {
      event.preventDefault();

      // Get canvas dimensions
      const rect = canvas.getBoundingClientRect();
      const mouseX = event.clientX - rect.left;
      const mouseY = event.clientY - rect.top;

      // Determine zoom direction
      const zoomFactor = event.deltaY > 0 ? 0.9 : 1.1;

      // Calculate new scale and offsets
      dispatch({
        type: "SET_CANVAS_PROPS",
        payload: {
          canvasScale: (prevScale) => prevScale * zoomFactor,
          canvasOffsetX: (prevOffsetX) =>
            prevOffsetX - (mouseX - canvasOffsetX) * (zoomFactor - 1),
          canvasOffsetY: (prevOffsetY) =>
            prevOffsetY - (mouseY - canvasOffsetY) * (zoomFactor - 1),
        },
      });
    };
    canvas.addEventListener("wheel", handleWheel);

    const redraw = debounce(drawTopography, 100);
    window.addEventListener("resize", redraw);

    return () => {
      window.removeEventListener("resize", redraw);
      canvas.removeEventListener("wheel", handleWheel);
    };
  }, []);

  useEffect(() => {
    console.log(canvasScale, canvasOffsetX, canvasOffsetY)
    drawTopography();
  }, [
    currentNode,
    canvasOffsetX,
    canvasOffsetY,
    canvasScale,
  ]);

  return (
    <div className="h-[80vh] border-2 border-gray-200 rounded mb-8 w-2/3">
      <canvas ref={canvasRef} />
    </div>
  );
};
