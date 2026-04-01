import { useEffect, useMemo, useRef } from "react";
import { Box } from "@mui/material";
import type { ChainTreeEntry } from "@/types";

const BLOCK_W = 52;
const BLOCK_H = 28;
const GAP_X = 12;
const GAP_Y = 6;
const COL_W = BLOCK_W + GAP_X;
const ROW_H = BLOCK_H + GAP_Y;

const MAIN_COLOR = "#90caf9";
const FORK_COLOR = "#ffb74d";
const TIP_COLOR = "#4caf50";
const LINE_COLOR = "#555";

interface LayoutBlock {
  entry: ChainTreeEntry;
  col: number;
  row: number;
  color: string;
}

export function ChainTreeView({
  entries,
  tipHash,
  tipCounts,
}: {
  entries: ChainTreeEntry[];
  tipHash?: string | null;
  tipCounts?: Record<string, number>;
}) {
  const layout = useMemo(() => {
    if (entries.length === 0) return { blocks: [] as LayoutBlock[], cols: 0, rows: 0 };

    const byHash = new Map<string, ChainTreeEntry>();
    for (const e of entries) byHash.set(e.hash, e);

    // Find main chain: walk from tip backward.
    // In tipCounts mode, pick the tip with the highest count.
    const mainSet = new Set<string>();
    let cur: string | null = null;
    if (tipCounts) {
      let bestCount = 0;
      for (const [hash, count] of Object.entries(tipCounts)) {
        if (byHash.has(hash) && count > bestCount) {
          bestCount = count;
          cur = hash;
        }
      }
    } else {
      cur = tipHash ?? null;
    }
    // If tip isn't in entries, find the highest block_number entry.
    if (!cur || !byHash.has(cur)) {
      let best: ChainTreeEntry | null = null;
      for (const e of entries) {
        if (!best || e.block_number > best.block_number) best = e;
      }
      cur = best?.hash ?? null;
    }
    while (cur && byHash.has(cur)) {
      mainSet.add(cur);
      cur = byHash.get(cur)!.prev_hash;
    }

    // Assign columns by block_number.
    const blockNums = [...new Set(entries.map((e) => e.block_number))].sort(
      (a, b) => a - b,
    );
    const colMap = new Map<number, number>();
    blockNums.forEach((bn, i) => colMap.set(bn, i));

    // Assign rows. Main chain always goes on row 0. Fork blocks go on
    // row 0 too if the column is free; otherwise they get bumped to a new
    // lane. Once a fork block is bumped, all its descendants stay in that
    // lane.
    const blocks: LayoutBlock[] = [];
    const colOccupied = new Map<number, Set<number>>(); // col → set of occupied rows
    const hashRow = new Map<string, number>(); // hash → assigned row
    let maxRow = 0;

    // Place main chain on row 0.
    for (const e of entries) {
      if (!mainSet.has(e.hash)) continue;
      const col = colMap.get(e.block_number)!;
      blocks.push({
        entry: e,
        col,
        row: 0,
        color: (tipCounts ? tipCounts[e.hash] !== undefined : e.hash === tipHash) ? TIP_COLOR : MAIN_COLOR,
      });
      hashRow.set(e.hash, 0);
      if (!colOccupied.has(col)) colOccupied.set(col, new Set());
      colOccupied.get(col)!.add(0);
    }

    // Sort fork blocks by block_number so parents are placed before children.
    const forkEntries = entries
      .filter((e) => !mainSet.has(e.hash))
      .sort((a, b) => a.block_number - b.block_number);

    for (const e of forkEntries) {
      const col = colMap.get(e.block_number)!;
      // Inherit lane from parent if parent is a fork block.
      const parentRow = e.prev_hash ? hashRow.get(e.prev_hash) : undefined;
      const inherited = parentRow !== undefined && parentRow > 0 ? parentRow : undefined;

      let row: number;
      if (inherited !== undefined) {
        // Descendant of a bumped fork — stay in parent's lane.
        row = inherited;
      } else {
        // Try row 0 first (share lane with main chain).
        const occ = colOccupied.get(col);
        if (!occ || !occ.has(0)) {
          row = 0;
        } else {
          // Column occupied — find lowest free lane.
          row = 1;
          while (occ.has(row)) row++;
        }
      }

      if (row > maxRow) maxRow = row;
      hashRow.set(e.hash, row);
      if (!colOccupied.has(col)) colOccupied.set(col, new Set());
      colOccupied.get(col)!.add(row);
      blocks.push({
        entry: e,
        col,
        row,
        color: FORK_COLOR,
      });
    }

    const cols = blockNums.length;
    const rows = maxRow + 1;
    return { blocks, cols, rows };
  }, [entries, tipHash, tipCounts]);

  const containerRef = useRef<HTMLDivElement>(null);

  // Scroll to the right (latest blocks) whenever entries change.
  useEffect(() => {
    const el = containerRef.current;
    if (el) el.scrollLeft = el.scrollWidth;
  }, [entries]);

  if (layout.blocks.length === 0) return null;

  const PAD_TOP = tipCounts ? 10 : 0;
  const svgW = layout.cols * COL_W;
  const svgH = layout.rows * ROW_H + PAD_TOP;

  // Build hash→position map for connectors.
  const posMap = new Map<string, { x: number; y: number }>();
  for (const b of layout.blocks) {
    posMap.set(b.entry.hash, {
      x: b.col * COL_W + BLOCK_W / 2,
      y: b.row * ROW_H + BLOCK_H / 2 + PAD_TOP,
    });
  }

  return (
    <Box ref={containerRef} sx={{ overflowX: "auto", mt: 0.5 }}>
      <svg width={svgW} height={svgH} style={{ display: "block" }}>
        {/* Connectors */}
        {layout.blocks.map((b) => {
          if (!b.entry.prev_hash) return null;
          const from = posMap.get(b.entry.prev_hash);
          const to = posMap.get(b.entry.hash);
          if (!from || !to) return null;
          return (
            <line
              key={`line-${b.entry.hash}`}
              x1={from.x + BLOCK_W / 2}
              y1={from.y}
              x2={to.x - BLOCK_W / 2}
              y2={to.y}
              stroke={LINE_COLOR}
              strokeWidth={1.5}
            />
          );
        })}
        {/* Blocks */}
        {layout.blocks.map((b) => {
          const x = b.col * COL_W;
          const y = b.row * ROW_H + PAD_TOP;
          return (
            <g key={`block-${b.entry.hash}`}>
              <rect
                x={x}
                y={y}
                width={BLOCK_W}
                height={BLOCK_H}
                rx={4}
                ry={4}
                fill="rgba(30,30,30,0.8)"
                stroke={b.color}
                strokeWidth={1.5}
              />
              <text
                x={x + BLOCK_W / 2}
                y={y + 11}
                textAnchor="middle"
                fill="#fff"
                fontSize={9}
                fontFamily="monospace"
              >
                {b.entry.block_number}
              </text>
              <text
                x={x + BLOCK_W / 2}
                y={y + 22}
                textAnchor="middle"
                fill={b.color}
                fontSize={8}
                fontFamily="monospace"
              >
                #{b.entry.hash}
              </text>
            </g>
          );
        })}
        {/* Tip count badges — overlaid on top-right of block */}
        {tipCounts && layout.blocks
          .filter((b) => tipCounts[b.entry.hash] !== undefined)
          .map((b) => {
            const bx = b.col * COL_W;
            const by = b.row * ROW_H + PAD_TOP;
            const label = String(tipCounts[b.entry.hash]);
            const padX = 4;
            const padY = 2;
            const badgeW = label.length * 7 + padX * 2;
            const badgeH = 14 + padY * 2;
            const rx = bx + BLOCK_W - badgeW + 4;
            const ry = by - badgeH / 2 + 2;
            return (
              <g key={`count-${b.entry.hash}`}>
                <rect
                  x={rx}
                  y={ry}
                  width={badgeW}
                  height={badgeH}
                  rx={3}
                  ry={3}
                  fill="rgba(0,0,0,0.7)"
                />
                <text
                  x={rx + badgeW / 2}
                  y={ry + badgeH / 2 + 4}
                  textAnchor="middle"
                  fill="#fff"
                  fontSize={12}
                  fontWeight="bold"
                  fontFamily="monospace"
                >
                  {label}
                </text>
              </g>
            );
          })}
      </svg>
    </Box>
  );
}
