import { IChainEB, IChainRB, IChainState } from "@/contexts/SimContext/types";
import { useMemo } from "react";

// Layout constants in world coordinates (pre-zoom). Linear placement:
// every slot is SLOT_WIDTH px from the previous one. MIN_CARD_GAP is only
// a safety floor for tightly clustered slots — at SLOT_WIDTH=20 it kicks
// in only when slots are within ~4 of each other.
export const SLOT_WIDTH = 20;
export const RB_WIDTH = 90;
export const RB_HEIGHT = 50;
export const EB_WIDTH = 90;
export const EB_HEIGHT = 52;
export const MIN_CARD_GAP = 5;
export const ROW_SPACING = 80;
export const RB_BASELINE_Y = 0;
// Reserve room for a few RB rows before EB stripe even if there are fewer.
export const EB_STRIPE_GAP = 120;

export type BlockRef =
  | { kind: "rb"; rb: IChainRB }
  | { kind: "eb"; eb: IChainEB };

export interface IBlockBox {
  x: number;
  y: number;
  width: number;
  height: number;
  ref: BlockRef;
}

export type EdgeKind = "parent" | "certifies" | "announces";

export interface IChainEdge {
  kind: EdgeKind;
  from: IBlockBox;
  to: IBlockBox;
}

export interface IChainLayout {
  rbBoxes: IBlockBox[];
  ebBoxes: IBlockBox[];
  edges: IChainEdge[];
  bounds: { minX: number; minY: number; maxX: number; maxY: number };
}

const EMPTY_LAYOUT: IChainLayout = {
  rbBoxes: [],
  ebBoxes: [],
  edges: [],
  bounds: { minX: 0, minY: 0, maxX: 0, maxY: 0 },
};

// Determine each RB's row index using the "longest chain on row 0, shorter
// chains take their own row for the diverging suffix" strategy described in
// the plan. Returns a Map<rbId, rowIndex> covering every visible RB.
const assignRows = (rbs: Map<string, IChainRB>): Map<string, number> => {
  const rowOf = new Map<string, number>();
  if (rbs.size === 0) return rowOf;

  // childOf[rbId] = list of children whose parentId === rbId
  const childOf = new Map<string, string[]>();
  for (const rb of rbs.values()) {
    if (rb.parentId && rbs.has(rb.parentId)) {
      const list = childOf.get(rb.parentId) ?? [];
      list.push(rb.id);
      childOf.set(rb.parentId, list);
    }
  }

  // Tips = RBs with no in-window child.
  const tipIds: string[] = [];
  for (const rb of rbs.values()) {
    if (!childOf.has(rb.id)) tipIds.push(rb.id);
  }

  // Walk back via parentId from each tip; collect the full chain (oldest first).
  type Chain = { ids: string[] };
  const chains: Chain[] = tipIds.map((tipId) => {
    const ids: string[] = [];
    let cur: string | undefined = tipId;
    while (cur && rbs.has(cur)) {
      ids.push(cur);
      const parent: string | undefined = rbs.get(cur)!.parentId;
      cur = parent && rbs.has(parent) ? parent : undefined;
    }
    ids.reverse();
    return { ids };
  });

  // Longest chain first → row 0; subsequent chains take next free row from
  // their first divergent block onward. Single-block "chains" whose RB has
  // no in-window parent are treated as genesis-orphans and packed onto row 0
  // together, so a trace with no parent edges renders as a single horizontal
  // strip instead of a vertical pile.
  chains.sort((a, b) => b.ids.length - a.ids.length);
  let nextRow = 0;
  for (const chain of chains) {
    const isOrphanSingleton =
      chain.ids.length === 1 && !rbs.get(chain.ids[0])!.parentId;
    let row = -1;
    for (const id of chain.ids) {
      if (rowOf.has(id)) continue;
      if (row === -1) row = isOrphanSingleton ? 0 : nextRow++;
      rowOf.set(id, row);
    }
  }

  // Any RB still unrowed (shouldn't happen, but be defensive).
  for (const id of rbs.keys()) {
    if (!rowOf.has(id)) rowOf.set(id, nextRow++);
  }

  return rowOf;
};

export const useChainLayout = (chain: IChainState): IChainLayout =>
  useMemo(() => computeChainLayout(chain), [chain]);

export const computeChainLayout = (chain: IChainState): IChainLayout => {
  const { rbs, ebs } = chain;
  if (rbs.size === 0 && ebs.size === 0) return EMPTY_LAYOUT;

  // Build a slot→x mapping that uses SLOT_WIDTH as the natural spacing but
  // enforces a minimum gap so cards at adjacent or same slots never overlap.
  // Both RB and EB cards at a given slot use the same x, keeping the cert /
  // announce arrows vertical.
  const allSlots = new Set<number>();
  rbs.forEach((rb) => allSlots.add(rb.slot));
  ebs.forEach((eb) => allSlots.add(eb.slot));
  const sortedSlots = Array.from(allSlots).sort((a, b) => a - b);
  const minSlot = sortedSlots[0];
  const slotX = new Map<number, number>();
  let prevX = -Infinity;
  const minStep = RB_WIDTH + MIN_CARD_GAP;
  for (const slot of sortedSlots) {
    const naturalX = (slot - minSlot) * SLOT_WIDTH;
    const x = prevX === -Infinity ? naturalX : Math.max(naturalX, prevX + minStep);
    slotX.set(slot, x);
    prevX = x;
  }

  const rowOf = assignRows(rbs);
  const maxRow = rowOf.size
    ? Math.max(...Array.from(rowOf.values()))
    : 0;

  const rbBoxesById = new Map<string, IBlockBox>();
  const rbBoxes: IBlockBox[] = [];
  rbs.forEach((rb) => {
    const row = rowOf.get(rb.id) ?? 0;
    const box: IBlockBox = {
      x: slotX.get(rb.slot)!,
      y: RB_BASELINE_Y + row * ROW_SPACING,
      width: RB_WIDTH,
      height: RB_HEIGHT,
      ref: { kind: "rb", rb },
    };
    rbBoxes.push(box);
    rbBoxesById.set(rb.id, box);
  });

  // EB stripe below all RB rows. If multiple EBs share a slot, stack them.
  const ebStripeY =
    RB_BASELINE_Y + (maxRow + 1) * ROW_SPACING + EB_STRIPE_GAP - ROW_SPACING;
  const perSlotCounts = new Map<number, number>();
  const ebBoxesById = new Map<string, IBlockBox>();
  const ebBoxes: IBlockBox[] = [];
  ebs.forEach((eb) => {
    const stackIdx = perSlotCounts.get(eb.slot) ?? 0;
    perSlotCounts.set(eb.slot, stackIdx + 1);
    const box: IBlockBox = {
      x: slotX.get(eb.slot)!,
      y: ebStripeY + stackIdx * (EB_HEIGHT + 12),
      width: EB_WIDTH,
      height: EB_HEIGHT,
      ref: { kind: "eb", eb },
    };
    ebBoxes.push(box);
    ebBoxesById.set(eb.id, box);
  });

  const edges: IChainEdge[] = [];
  rbs.forEach((rb) => {
    const rbBox = rbBoxesById.get(rb.id)!;
    if (rb.parentId) {
      const parentBox = rbBoxesById.get(rb.parentId);
      if (parentBox) edges.push({ kind: "parent", from: parentBox, to: rbBox });
    }
    if (rb.certifiesEbId) {
      const ebBox = ebBoxesById.get(rb.certifiesEbId);
      if (ebBox) edges.push({ kind: "certifies", from: rbBox, to: ebBox });
    }
    if (rb.announcesEbId) {
      const ebBox = ebBoxesById.get(rb.announcesEbId);
      if (ebBox) edges.push({ kind: "announces", from: rbBox, to: ebBox });
    }
  });

  // Invert vertically: the longest chain (row 0) and the EB stripe were built
  // with positive y going down, longest at top. Mirror around the maximum y
  // so the longest chain sits at the BOTTOM and shorter forks / EB stripe
  // rise above it. The Global Stats overlay hangs from the upper-left, so
  // keeping the main chain low keeps it out from under the panel.
  let preFlipMaxY = 0;
  for (const box of [...rbBoxes, ...ebBoxes]) {
    if (box.y + box.height > preFlipMaxY) preFlipMaxY = box.y + box.height;
  }
  for (const box of [...rbBoxes, ...ebBoxes]) {
    box.y = preFlipMaxY - box.y - box.height;
  }

  // Bounds — include card extents.
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;
  for (const box of [...rbBoxes, ...ebBoxes]) {
    if (box.x < minX) minX = box.x;
    if (box.y < minY) minY = box.y;
    if (box.x + box.width > maxX) maxX = box.x + box.width;
    if (box.y + box.height > maxY) maxY = box.y + box.height;
  }

  return { rbBoxes, ebBoxes, edges, bounds: { minX, minY, maxX, maxY } };
};
