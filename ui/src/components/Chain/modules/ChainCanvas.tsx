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
// Voting progress visualisation. Threshold is the (likely) certification
// quorum at 75%. Once crossed, the EB recolors to votes-purple.
const CERT_THRESHOLD = 0.75;
const VOTES_COLOR = EMessageColor.VOTES;
const EB_CERTIFIED_FILL = "#f3e8ff";

// =============================================================================
// FIXME: VOTING-PROGRESS PROXY
// -----------------------------------------------------------------------------
// Progress = min(1, voteWeight / totalVotes)
//
//   * `voteWeight` is summed in the aggregator (timelineAggregation.ts):
//     - simulator: sum of lottery hit counts (values in the `{ebId: count}`
//       weight map);
//     - prototype: sum of `Vote.weight` (stake fraction in [0,1]) when
//       present, otherwise 1 per vote.
//   * `totalVotes` comes from the active scenario (`scenarios.json`). For
//     sim-rs wfa-ls the natural value is 500 (persistent 400 +
//     non-persistent 100). When unset (prototype case) we default to 1.0
//     since prototype weights are already stake fractions summing to ≤1.
//
// Not yet protocol-correct:
//   * The 75% threshold (CERT_THRESHOLD above) is still a placeholder;
//     sim-rs uses 300/500 = 60% by default. Surface via the trace/config
//     once it stabilises.
// =============================================================================
const computeVotingProgress = (
  voteWeight: number | undefined,
  totalVotes: number,
): number => {
  if (totalVotes <= 0) return 0;
  return Math.min(1, (voteWeight ?? 0) / totalVotes);
};

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
  votingProgress?: number,
) => {
  const certified = votingProgress !== undefined && votingProgress >= CERT_THRESHOLD;
  const fill =
    box.ref.kind === "rb"
      ? RB_FILL
      : certified
        ? EB_CERTIFIED_FILL
        : EB_FILL;
  const border =
    box.ref.kind === "rb"
      ? RB_BORDER
      : certified
        ? VOTES_COLOR
        : EB_BORDER;

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

    if (votingProgress !== undefined) {
      // Align horizontally with the text rows (same padX) and place the bar
      // one "row" below the last text line so the vertical gap matches the
      // 12px line spacing above.
      const barH = 4;
      const barX = box.x + padX;
      const barW = box.width - padX * 2;
      const barY = textY + 12;
      // Track
      ctx.fillStyle = "#e5e7eb";
      ctx.fillRect(barX, barY, barW, barH);
      // Fill (purple = votes colour)
      ctx.fillStyle = VOTES_COLOR;
      ctx.fillRect(barX, barY, barW * Math.min(1, votingProgress), barH);
      // 75% threshold tick
      const tickX = barX + barW * CERT_THRESHOLD;
      ctx.strokeStyle = TEXT_COLOR;
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(tickX, barY - 2);
      ctx.lineTo(tickX, barY + barH + 2);
      ctx.stroke();
    }
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
      allScenarios,
      activeScenario,
    },
    dispatch,
  } = useSimContext();

  // Per-pipeline total vote weight (the certification denominator). When
  // the scenario sets `totalVotes` we trust it (e.g. 500 for sim-rs wfa-ls
  // configured with persistent 400 + non-persistent 100). Otherwise we
  // assume per-vote weights already sum to ≤1.0 — the prototype's
  // eventual stake-weighted shape. See voting-progress FIXME above.
  const totalVotes = useMemo(() => {
    const s = allScenarios.find((sc) => sc.name === activeScenario);
    return s?.totalVotes ?? 1.0;
  }, [allScenarios, activeScenario]);

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

  // Project the leading edge to where a new RB at the current slot would
  // *naturally* land in the layout — i.e. `(currentSlot - minSlot) *
  // SLOT_WIDTH`. We map `currentTime` (which is wall-clock — epoch seconds
  // for Loki, trace-relative for the simulator) into slot space via
  // `chain.slotZeroTime` (derived from the first observed RB as
  // `time_s - slot`). Without this conversion, Loki traces would push the
  // leading edge billions of pixels off-screen.
  //
  // This matches the layout's own coordinate system, so a new block lands
  // exactly where the projection was pointing (no jump when there's no
  // min-gap clamping). Clamped to at least the right edge of the tip so
  // the dashed edge never sits behind the tip in min-gap clusters.
  const leadingEdgeX = useMemo(() => {
    if (!tipRB || tipRB.ref.kind !== "rb") return undefined;
    if (chain.slotZeroTime === undefined) {
      return tipRB.x + tipRB.width;
    }
    const currentSlot = currentTime - chain.slotZeroTime;
    const natural = (currentSlot - layout.minSlot) * SLOT_WIDTH;
    return Math.max(tipRB.x + tipRB.width, natural);
  }, [tipRB, currentTime, layout.minSlot, chain.slotZeroTime]);
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
    for (const box of layout.ebBoxes) {
      const progress =
        box.ref.kind === "eb"
          ? computeVotingProgress(box.ref.eb.voteCount, totalVotes)
          : undefined;
      drawBlock(ctx, box, isSelected(selectedBlock, box), progress);
    }
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
    currentTime,
    totalVotes,
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
