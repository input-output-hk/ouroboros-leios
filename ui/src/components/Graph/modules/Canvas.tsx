"use client";

import { useGraphContext } from "@/contexts/GraphContext/context";
import debounce from "debounce";
import { FC, useCallback, useEffect, useRef } from "react";
import { useHandlers } from "../hooks/useHandlers";
import { getOffsetCoordinates, isClickOnNode } from "../utils";

export const Canvas: FC = () => {
  const { drawTopography } = useHandlers();
  const {
    state: { canvasRef, canvasOffsetX, canvasOffsetY, canvasScale, topography },
    dispatch,
  } = useGraphContext();
  const isDragging = useRef(false);
  const dragStart = useRef({ x: 0, y: 0 });

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) {
      return;
    }

    const width = canvas.parentElement?.getBoundingClientRect().width || 1024;
    const height = canvas.parentElement?.getBoundingClientRect().height || 800;
    const { offsetX, offsetY } = getOffsetCoordinates(
      topography,
      width,
      height,
      canvasScale,
    );
    
    dispatch({
      type: "SET_CANVAS_PROPS",
      payload: {
        canvasOffsetX: offsetX,
        canvasOffsetY: offsetY,
      },
    });
  }, []);

  const handleClick = useCallback(
    (ev: MouseEvent) => {
      const canvas = canvasRef.current;
      if (!canvas || ev.target !== canvas || isDragging.current) {
        return;
      }

      const rect = canvas.getBoundingClientRect();
      const x = ev.clientX - rect.left;
      const y = ev.clientY - rect.top;
      console.log(canvasScale);
      const { node } = isClickOnNode(
        x,
        y,
        topography,
        (2 / canvasScale) * 6,
        canvasOffsetX,
        canvasOffsetY,
        canvasScale,
      );

      dispatch({ type: "SET_CURRENT_NODE", payload: node });
    },
    [canvasScale, canvasOffsetX, canvasOffsetY],
  );

  const handleWheel = useCallback(
    (ev: WheelEvent) => {
      const canvas = canvasRef.current;
      if (!canvas || ev.target !== canvas) {
        return;
      }

      // Get canvas dimensions
      const rect = canvas.getBoundingClientRect();
      const mouseX = ev.clientX - rect.left;
      const mouseY = ev.clientY - rect.top;

      // Determine zoom direction
      const zoomFactor = ev.deltaY > 0 ? 0.9 : 1.1;

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
    },
    [canvasOffsetX, canvasOffsetY],
  );

  const handleMouseDown = useCallback((ev: MouseEvent) => {
    const canvas = canvasRef.current;
    if (!canvas || ev.target !== canvas) {
      return;
    }

    isDragging.current = true;
    dragStart.current = { x: ev.clientX, y: ev.clientY };
  }, []);

  const handleMouseMove = useCallback((ev: MouseEvent) => {
    const canvas = canvasRef.current;
    if (!canvas || ev.target !== canvas || !isDragging.current) {
      return;
    }

    const deltaX = ev.clientX - dragStart.current.x;
    const deltaY = ev.clientY - dragStart.current.y;

    dispatch({
      type: "SET_CANVAS_PROPS",
      payload: {
        canvasOffsetX(prev) {
          return prev + deltaX;
        },
        canvasOffsetY(prev) {
          return prev + deltaY;
        },
      },
    });

    dragStart.current = { x: ev.clientX, y: ev.clientY };
  }, []);

  const handleMouseUp = useCallback((ev: MouseEvent) => {
    const canvas = canvasRef.current;
    if (!canvas || ev.target !== canvas) {
      return;
    }

    isDragging.current = false;
  }, []);

  useEffect(() => {
    drawTopography();
    
    document.addEventListener("mousedown", handleMouseDown);
    document.addEventListener("mousemove", handleMouseMove);
    document.addEventListener("mouseup", handleMouseUp);
    document.addEventListener("click", handleClick);
    document.addEventListener("wheel", handleWheel);

    const redraw = debounce(drawTopography, 100);
    document.addEventListener("resize", redraw);

    return () => {
      document.removeEventListener("resize", redraw);
      document.removeEventListener("mousedown", handleMouseDown);
      document.removeEventListener("mousemove", handleMouseMove);
      document.removeEventListener("mouseup", handleMouseUp);
      document.removeEventListener("click", handleClick);
      document.removeEventListener("wheel", handleWheel);
    };
  }, [drawTopography, handleClick, handleWheel]);

  return (
    <div className="h-[80vh] border-2 border-gray-200 rounded mb-8 w-2/3">
      <canvas ref={canvasRef} />
    </div>
  );
};
