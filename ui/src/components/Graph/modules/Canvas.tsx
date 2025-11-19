"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import debounce from "debounce";
import { FC, useCallback, useEffect, useRef } from "react";
import { useHandlers } from "../hooks/useHandlers";
import { getOffsetCoordinates, isClickOnNode } from "../utils";

export const Canvas: FC = () => {
  const { drawTopography } = useHandlers();
  const {
    state: {
      graph: {
        canvasOffsetX,
        canvasOffsetY,
        canvasRef,
        canvasScale,
        currentNode,
      },
      topography,
    },
    dispatch,
  } = useSimContext();
  const isDragging = useRef(false);
  const dragStart = useRef({ x: 0, y: 0 });
  const hasMoved = useRef(false);
  const pointerCapture = useRef<number | undefined>(undefined);

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
    (ev: PointerEvent) => {
      const canvas = canvasRef.current;
      if (!canvas || ev.target !== canvas) {
        return;
      }

      // Only handle clicks if we weren't dragging
      if (hasMoved.current) {
        return;
      }

      const rect = canvas.getBoundingClientRect();
      const x = ev.clientX - rect.left;
      const y = ev.clientY - rect.top;
      const { node, clicked } = isClickOnNode(
        x,
        y,
        topography,
        (2 / canvasScale) * 6,
        canvasOffsetX,
        canvasOffsetY,
        canvasScale,
      );

      if (clicked && node) {
        dispatch({
          type: "SET_CURRENT_NODE",
          payload: currentNode === node ? undefined : node,
        });
      } else {
        // Click on background - unset current node
        dispatch({
          type: "SET_CURRENT_NODE",
          payload: undefined,
        });
      }
    },
    [canvasScale, currentNode, canvasOffsetX, canvasOffsetY],
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

  const handlePointerDown = useCallback((ev: PointerEvent) => {
    const canvas = canvasRef.current;
    if (!canvas || ev.target !== canvas || ev.button !== 0) {
      return;
    }

    isDragging.current = true;
    hasMoved.current = false;
    canvas.setPointerCapture(ev.pointerId);
    pointerCapture.current = ev.pointerId;
    dragStart.current = { x: ev.clientX, y: ev.clientY };
  }, []);

  const handlePointerMove = useCallback((ev: PointerEvent) => {
    const canvas = canvasRef.current;
    if (!canvas || ev.target !== canvas || !isDragging.current) {
      return;
    }

    const deltaX = ev.clientX - dragStart.current.x;
    const deltaY = ev.clientY - dragStart.current.y;

    // Mark that we've moved if there's significant movement
    if (Math.abs(deltaX) > 2 || Math.abs(deltaY) > 2) {
      hasMoved.current = true;
    }

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

  const handlePointerUp = useCallback((ev: PointerEvent) => {
    const canvas = canvasRef.current;
    if (!canvas || ev.target !== canvas || ev.button !== 0) {
      return;
    }

    isDragging.current = false;
    pointerCapture.current = undefined;
    canvas.releasePointerCapture(ev.pointerId);
  }, []);

  useEffect(() => {
    drawTopography();

    const canvas = canvasRef.current;
    if (!canvas) {
      return;
    }

    canvas.addEventListener("pointerdown", handlePointerDown);
    canvas.addEventListener("pointermove", handlePointerMove);
    canvas.addEventListener("pointerup", handlePointerUp);
    canvas.addEventListener("pointerup", handleClick);
    canvas.addEventListener("wheel", handleWheel);

    const redraw = debounce(drawTopography, 100);
    document.addEventListener("resize", redraw);

    return () => {
      document.removeEventListener("resize", redraw);
      canvas.removeEventListener("pointerdown", handlePointerDown);
      canvas.removeEventListener("pointermove", handlePointerMove);
      canvas.removeEventListener("pointerup", handlePointerUp);
      canvas.removeEventListener("pointerup", handleClick);
      canvas.removeEventListener("wheel", handleWheel);
    };
  }, [drawTopography, handleClick, handleWheel]);

  return <canvas ref={canvasRef} />;
};
