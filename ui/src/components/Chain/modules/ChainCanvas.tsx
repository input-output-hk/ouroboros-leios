"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import { ISelectedBlock } from "@/contexts/SimContext/types";
import { EMessageColor } from "@/utils/colors";
import { FC, useCallback, useEffect, useMemo, useRef, useState } from "react";
import {
  IBlockBox,
  IChainEdge,
  IChainLayout,
  SLOT_WIDTH,
  useChainLayout,
} from "../hooks/useChainLayout";

// Reserve space for the floating overlays in SimWrapper: the playback bar
// at the bottom and a margin on the right. The tip is right-aligned on
// first view; the soft-scroll logic keeps the leading edge from slipping
// past the right padding while playing.
const PADDING_RIGHT = 40;
const PADDING_BOTTOM = 150;

const BG_COLOR = "#ffffff";
const RB_FILL = "#fff5f5";
const RB_BORDER = EMessageColor.RB;
const EB_FILL = "#eef4ff";
const EB_BORDER = EMessageColor.EB;
const SELECTED_BORDER = "#1f2937";
const PARENT_EDGE = "#9ca3af";
const CERT_EDGE = "#f97316";
const ANNOUNCE_EDGE = "#3b82f6";
const TEXT_COLOR = "#111827";
const SUBTLE_TEXT = "#6b7280";

const shortId = (id: string) => (id.length > 8 ? `${id.slice(0, 8)}…` : id);

const isSelected = (
  sel: ISelectedBlock | undefined,
  box: IBlockBox,
): boolean => {
  if (!sel) return false;
  if (box.ref.kind === "rb")
    return sel.kind === "rb" && sel.id === box.ref.rb.id;
  return sel.kind === "eb" && sel.id === box.ref.eb.id;
};

const drawEdge = (ctx: CanvasRenderingContext2D, edge: IChainEdge) => {
  const { from, to, kind } = edge;
  const x1 = from.x + from.width / 2;
  const y1 = from.y + from.height / 2;
  const x2 = to.x + to.width / 2;
  const y2 = to.y + to.height / 2;

  ctx.save();
  if (kind === "parent") {
    ctx.strokeStyle = PARENT_EDGE;
    ctx.lineWidth = 2;
    ctx.setLineDash([]);
  } else if (kind === "certifies") {
    ctx.strokeStyle = CERT_EDGE;
    ctx.lineWidth = 1.5;
    ctx.setLineDash([]);
  } else {
    ctx.strokeStyle = ANNOUNCE_EDGE;
    ctx.lineWidth = 1.5;
    ctx.setLineDash([4, 4]);
  }

  ctx.beginPath();
  if (kind === "parent") {
    // Mostly horizontal with a slight curve to handle row jumps.
    const midX = (x1 + x2) / 2;
    ctx.moveTo(x1, y1);
    ctx.bezierCurveTo(midX, y1, midX, y2, x2, y2);
  } else {
    // Curve down from RB to EB.
    const midY = (y1 + y2) / 2;
    ctx.moveTo(x1, y1);
    ctx.bezierCurveTo(x1, midY, x2, midY, x2, y2);
  }
  ctx.stroke();

  // Arrowhead at target.
  const angle =
    kind === "parent"
      ? Math.atan2(y2 - y1, x2 - x1)
      : Math.atan2(y2 - (y1 + y2) / 2, x2 - x2);
  // For curved RB→EB the tangent is near-vertical at the target; use a simple
  // downward arrow head.
  const headLen = 8;
  const headAngle = Math.PI / 7;
  if (kind === "parent") {
    ctx.beginPath();
    ctx.moveTo(x2, y2);
    ctx.lineTo(
      x2 - headLen * Math.cos(angle - headAngle),
      y2 - headLen * Math.sin(angle - headAngle),
    );
    ctx.moveTo(x2, y2);
    ctx.lineTo(
      x2 - headLen * Math.cos(angle + headAngle),
      y2 - headLen * Math.sin(angle + headAngle),
    );
    ctx.stroke();
  } else {
    ctx.beginPath();
    ctx.moveTo(x2, y2);
    ctx.lineTo(x2 - 4, y2 - 8);
    ctx.moveTo(x2, y2);
    ctx.lineTo(x2 + 4, y2 - 8);
    ctx.stroke();
  }
  ctx.restore();

  // Edge label, near the source for cert/announce.
  if (kind !== "parent") {
    ctx.save();
    ctx.fillStyle = kind === "certifies" ? CERT_EDGE : ANNOUNCE_EDGE;
    ctx.font = "10px ui-sans-serif, system-ui";
    ctx.textAlign = "center";
    ctx.fillText(
      kind === "certifies" ? "certifies" : "announces",
      (x1 + x2) / 2,
      (y1 + y2) / 2 - 2,
    );
    ctx.restore();
  }
};

const drawBlock = (
  ctx: CanvasRenderingContext2D,
  box: IBlockBox,
  selected: boolean,
) => {
  const fill = box.ref.kind === "rb" ? RB_FILL : EB_FILL;
  const border = box.ref.kind === "rb" ? RB_BORDER : EB_BORDER;

  ctx.save();
  ctx.fillStyle = fill;
  ctx.strokeStyle = selected ? SELECTED_BORDER : border;
  ctx.lineWidth = selected ? 2.5 : 1.5;

  const r = 6;
  ctx.beginPath();
  ctx.moveTo(box.x + r, box.y);
  ctx.lineTo(box.x + box.width - r, box.y);
  ctx.quadraticCurveTo(box.x + box.width, box.y, box.x + box.width, box.y + r);
  ctx.lineTo(box.x + box.width, box.y + box.height - r);
  ctx.quadraticCurveTo(
    box.x + box.width,
    box.y + box.height,
    box.x + box.width - r,
    box.y + box.height,
  );
  ctx.lineTo(box.x + r, box.y + box.height);
  ctx.quadraticCurveTo(
    box.x,
    box.y + box.height,
    box.x,
    box.y + box.height - r,
  );
  ctx.lineTo(box.x, box.y + r);
  ctx.quadraticCurveTo(box.x, box.y, box.x + r, box.y);
  ctx.closePath();
  ctx.fill();
  ctx.stroke();

  ctx.fillStyle = TEXT_COLOR;
  ctx.font = "bold 11px ui-monospace, monospace";
  ctx.textAlign = "left";
  ctx.textBaseline = "top";
  const padX = 6;
  let textY = box.y + 5;
  if (box.ref.kind === "rb") {
    const rb = box.ref.rb;
    ctx.fillText(`RB ${shortId(rb.id)}`, box.x + padX, textY);
    textY += 13;
    ctx.font = "10px ui-sans-serif, system-ui";
    ctx.fillStyle = SUBTLE_TEXT;
    const headerLine =
      rb.blockNumber !== undefined
        ? `slot ${rb.slot} · #${rb.blockNumber}`
        : `slot ${rb.slot}`;
    ctx.fillText(headerLine, box.x + padX, textY);
    textY += 12;
    ctx.fillText(rb.producer, box.x + padX, textY);
    textY += 12;
    ctx.fillText(`${(rb.sizeBytes / 1024).toFixed(1)} KB`, box.x + padX, textY);
  } else {
    const eb = box.ref.eb;
    ctx.fillText(`EB ${shortId(eb.id)}`, box.x + padX, textY);
    textY += 13;
    ctx.font = "10px ui-sans-serif, system-ui";
    ctx.fillStyle = SUBTLE_TEXT;
    ctx.fillText(`slot ${eb.slot}`, box.x + padX, textY);
    textY += 12;
    ctx.fillText(`${(eb.sizeBytes / 1024).toFixed(1)} KB`, box.x + padX, textY);
  }
  ctx.restore();
};

const findHit = (
  layout: IChainLayout,
  wx: number,
  wy: number,
): IBlockBox | undefined => {
  // RBs first (drawn on top of EBs).
  for (const box of layout.rbBoxes) {
    if (
      wx >= box.x &&
      wx <= box.x + box.width &&
      wy >= box.y &&
      wy <= box.y + box.height
    ) {
      return box;
    }
  }
  for (const box of layout.ebBoxes) {
    if (
      wx >= box.x &&
      wx <= box.x + box.width &&
      wy >= box.y &&
      wy <= box.y + box.height
    ) {
      return box;
    }
  }
  return undefined;
};

export const ChainCanvas: FC = () => {
  const {
    state: {
      aggregatedData: { chain },
      selectedBlock,
      isPlaying,
      currentTime,
    },
    dispatch,
  } = useSimContext();

  const layout = useChainLayout(chain);

  // Rightmost RB by slot, anchor for the continuously growing leading edge.
  const tipRB = useMemo(() => {
    let best: IBlockBox | undefined;
    for (const box of layout.rbBoxes) {
      if (box.ref.kind !== "rb") continue;
      if (
        !best ||
        box.ref.rb.slot >
          (best.ref as { kind: "rb"; rb: { slot: number } }).rb.slot
      ) {
        best = box;
      }
    }
    return best;
  }, [layout]);

  // Pixels per slot for the projection: matches the displayed block-to-block
  // spacing so the leading edge advances at the same visual rate as actual
  // blocks in the chain. We use the average across the visible chain (last
  // box vs first box) since pair-by-pair rates vary with min-gap clamping.
  // Falls back to the natural SLOT_WIDTH when there's only one RB.
  const pxPerSlot = useMemo(() => {
    let first: IBlockBox | undefined;
    let last: IBlockBox | undefined;
    for (const box of layout.rbBoxes) {
      if (box.ref.kind !== "rb") continue;
      const slot = box.ref.rb.slot;
      if (
        !first ||
        slot < (first.ref as { kind: "rb"; rb: { slot: number } }).rb.slot
      )
        first = box;
      if (
        !last ||
        slot > (last.ref as { kind: "rb"; rb: { slot: number } }).rb.slot
      )
        last = box;
    }
    if (!first || !last || first === last) return SLOT_WIDTH;
    const dSlot =
      (last.ref as { kind: "rb"; rb: { slot: number } }).rb.slot -
      (first.ref as { kind: "rb"; rb: { slot: number } }).rb.slot;
    if (dSlot <= 0) return SLOT_WIDTH;
    return (last.x - first.x) / dSlot;
  }, [layout]);

  const leadingEdgeX = useMemo(() => {
    if (!tipRB || tipRB.ref.kind !== "rb") return undefined;
    const extraSlots = Math.max(0, currentTime - tipRB.ref.rb.slot);
    return tipRB.x + tipRB.width + extraSlots * pxPerSlot;
  }, [tipRB, currentTime, pxPerSlot]);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const wrapperRef = useRef<HTMLDivElement>(null);

  const [scale, setScale] = useState(1);
  const [offsetX, setOffsetX] = useState(0);
  const [offsetY, setOffsetY] = useState(0);
  const [size, setSize] = useState({ w: 1024, h: 600 });

  const isDragging = useRef(false);
  const hasMoved = useRef(false);
  const dragStart = useRef({ x: 0, y: 0 });

  // Track wrapper size for HiDPI canvas sizing.
  useEffect(() => {
    const wrapper = wrapperRef.current;
    if (!wrapper) return;
    const update = () => {
      const rect = wrapper.getBoundingClientRect();
      setSize({ w: rect.width, h: rect.height });
    };
    update();
    const ro = new ResizeObserver(update);
    ro.observe(wrapper);
    return () => ro.disconnect();
  }, []);

  // Initial placement: right-align the chain — pin the tip (or the
  // continuously growing leading edge if it extends beyond the tip) to the
  // right safe area, and bottom-align the longest row. The soft-scroll
  // logic keeps it there during play; on pause the user can pan freely.
  const hasFitted = useRef(false);
  useEffect(() => {
    if (hasFitted.current) return;
    const { minX, maxX, maxY } = layout.bounds;
    if (!isFinite(minX)) return;
    const effMaxX =
      leadingEdgeX !== undefined ? Math.max(maxX, leadingEdgeX) : maxX;
    setOffsetX(size.w - PADDING_RIGHT - effMaxX * scale);
    setOffsetY(size.h - PADDING_BOTTOM - maxY * scale);
    hasFitted.current = true;
  }, [layout.bounds, leadingEdgeX, size, scale]);

  // While playing, ensure the newest block stays visible: if the leading
  // edge (tip RB + elapsed-time extension) drifts past the right edge of
  // the safe area, scroll left just enough to bring it back. Drag/zoom is
  // not blocked — only the right-overflow case triggers an adjustment.
  useEffect(() => {
    if (!isPlaying) return;
    if (leadingEdgeX === undefined) return;
    setOffsetX((prev) => {
      const leadingScreenX = leadingEdgeX * scale + prev;
      const rightEdge = size.w - PADDING_RIGHT;
      if (leadingScreenX > rightEdge) {
        return rightEdge - leadingEdgeX * scale;
      }
      return prev;
    });
  }, [isPlaying, leadingEdgeX, scale, size]);

  // Render.
  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const dpr = window.devicePixelRatio || 1;
    canvas.width = size.w * dpr;
    canvas.height = size.h * dpr;
    canvas.style.width = `${size.w}px`;
    canvas.style.height = `${size.h}px`;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

    ctx.fillStyle = BG_COLOR;
    ctx.fillRect(0, 0, size.w, size.h);

    ctx.save();
    ctx.translate(offsetX, offsetY);
    ctx.scale(scale, scale);

    for (const edge of layout.edges) drawEdge(ctx, edge);
    // Continuously growing leading edge: from the tip RB's right side to a
    // point projected forward from currentTime. Dashed so it's clearly
    // "pending" rather than a real parent link.
    if (
      tipRB &&
      leadingEdgeX !== undefined &&
      leadingEdgeX > tipRB.x + tipRB.width
    ) {
      ctx.save();
      ctx.strokeStyle = PARENT_EDGE;
      ctx.lineWidth = 2;
      ctx.setLineDash([6, 4]);
      ctx.beginPath();
      const midY = tipRB.y + tipRB.height / 2;
      ctx.moveTo(tipRB.x + tipRB.width, midY);
      ctx.lineTo(leadingEdgeX, midY);
      ctx.stroke();
      ctx.restore();
    }
    for (const box of layout.ebBoxes)
      drawBlock(ctx, box, isSelected(selectedBlock, box));
    for (const box of layout.rbBoxes)
      drawBlock(ctx, box, isSelected(selectedBlock, box));

    ctx.restore();
  }, [
    layout,
    scale,
    offsetX,
    offsetY,
    size,
    selectedBlock,
    tipRB,
    leadingEdgeX,
  ]);

  const handlePointerDown = useCallback(
    (ev: React.PointerEvent<HTMLCanvasElement>) => {
      if (ev.button !== 0) return;
      isDragging.current = true;
      hasMoved.current = false;
      dragStart.current = { x: ev.clientX, y: ev.clientY };
      ev.currentTarget.setPointerCapture(ev.pointerId);
    },
    [],
  );

  const handlePointerMove = useCallback(
    (ev: React.PointerEvent<HTMLCanvasElement>) => {
      if (!isDragging.current) return;
      const dx = ev.clientX - dragStart.current.x;
      const dy = ev.clientY - dragStart.current.y;
      if (Math.abs(dx) > 2 || Math.abs(dy) > 2) {
        hasMoved.current = true;
      }
      setOffsetX((prev) => prev + dx);
      setOffsetY((prev) => prev + dy);
      dragStart.current = { x: ev.clientX, y: ev.clientY };
    },
    [],
  );

  const handlePointerUp = useCallback(
    (ev: React.PointerEvent<HTMLCanvasElement>) => {
      if (ev.button !== 0) return;
      isDragging.current = false;
      ev.currentTarget.releasePointerCapture(ev.pointerId);

      if (hasMoved.current) return;
      const canvas = canvasRef.current;
      if (!canvas) return;
      const rect = canvas.getBoundingClientRect();
      const cx = ev.clientX - rect.left;
      const cy = ev.clientY - rect.top;
      const wx = (cx - offsetX) / scale;
      const wy = (cy - offsetY) / scale;
      const hit = findHit(layout, wx, wy);
      if (!hit) {
        if (selectedBlock) {
          dispatch({ type: "SET_SELECTED_BLOCK", payload: undefined });
        }
        return;
      }
      const next: ISelectedBlock =
        hit.ref.kind === "rb"
          ? { kind: "rb", id: hit.ref.rb.id }
          : { kind: "eb", id: hit.ref.eb.id };
      const same =
        selectedBlock &&
        selectedBlock.kind === next.kind &&
        selectedBlock.id === next.id;
      dispatch({
        type: "SET_SELECTED_BLOCK",
        payload: same ? undefined : next,
      });
    },
    [layout, offsetX, offsetY, scale, selectedBlock, dispatch],
  );

  const handleWheel = useCallback((ev: WheelEvent) => {
    ev.preventDefault();
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const mx = ev.clientX - rect.left;
    const my = ev.clientY - rect.top;
    const factor = ev.deltaY > 0 ? 0.9 : 1.1;
    setScale((prev) => prev * factor);
    setOffsetX((prev) => prev - (mx - prev) * (factor - 1));
    setOffsetY((prev) => prev - (my - prev) * (factor - 1));
  }, []);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    canvas.addEventListener("wheel", handleWheel, { passive: false });
    return () => canvas.removeEventListener("wheel", handleWheel);
  }, [handleWheel]);

  const empty = useMemo(
    () => layout.rbBoxes.length === 0 && layout.ebBoxes.length === 0,
    [layout],
  );

  return (
    <div ref={wrapperRef} className="absolute inset-0">
      <canvas
        ref={canvasRef}
        onPointerDown={handlePointerDown}
        onPointerMove={handlePointerMove}
        onPointerUp={handlePointerUp}
        className="block cursor-grab active:cursor-grabbing"
      />
      {empty ? (
        <div className="absolute inset-0 flex items-center justify-center pointer-events-none">
          <p className="text-gray-500 text-sm">
            No blocks yet at this point in the timeline.
          </p>
        </div>
      ) : null}
    </div>
  );
};
