// Parses the nested checkbox list used as the single source of truth for the
// protocol status diagram and matrix.
//
//   - Component name @x,y          <- level 1: a component, optional diagram anchor
//     - [x] Stage: note            <- level 2: one entry per stage, optional note
//       - [~] Some detail          <- level 3: details, shown in the tooltip only
//
// Marks: [x] done · [~] ongoing · [?] open question · [-] missing · [ ] not started

export type Mark = "done" | "ongoing" | "missing" | "open" | "empty";

export type Detail = {
  mark: Mark;
  text: string;
};

export type Cell = {
  mark: Mark;
  note?: string;
  details: Detail[];
};

export type Row = {
  id: string;
  name: string;
  anchor?: { x: number; y: number };
  cells: Cell[]; // aligned with the stages passed to parseStatus
};

const MARKS: Record<string, Mark> = {
  x: "done",
  X: "done",
  "~": "ongoing",
  "?": "open",
  "-": "missing",
  " ": "empty",
  "": "empty",
};

const ITEM_RE = /^(\s*)[-*]\s+(.*?)\s*$/;
const CHECKBOX_RE = /^\[(.?)\]\s*(.*)$/;
const ANCHOR_RE = /\s*@\s*(-?[\d.]+)\s*,\s*(-?[\d.]+)\s*$/;

/** Splits `Design: some note` into its label and optional note. */
function splitNote(text: string): { label: string; note?: string } {
  const i = text.indexOf(":");
  if (i === -1) return { label: text.trim() };
  const note = text.slice(i + 1).trim();
  return { label: text.slice(0, i).trim(), note: note || undefined };
}

function slugify(name: string): string {
  return name
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/(^-|-$)/g, "");
}

function fail(lineNo: number, line: string, message: string): never {
  throw new Error(
    `ProtocolStatus: ${message} — line ${lineNo} of the status list: "${line.trim()}"`,
  );
}

function parseCheckbox(
  lineNo: number,
  line: string,
  text: string,
): { mark: Mark; label: string; note?: string } {
  const m = CHECKBOX_RE.exec(text);
  if (!m) fail(lineNo, line, "expected a checkbox, e.g. `- [x] Design`");
  const mark = MARKS[m[1]];
  if (!mark) {
    fail(
      lineNo,
      line,
      `unknown mark \`[${m[1]}]\`, expected one of [x] [~] [?] [-] [ ]`,
    );
  }
  return { mark, ...splitNote(m[2]) };
}

/** Comparison key for correlating plan items with status details by name. */
export function nameKey(text: string): string {
  return text
    .toLowerCase()
    .replace(/\(\?\)/g, "")
    .replace(/[^a-z0-9]+/g, " ")
    .trim();
}

export function parseStatus(source: string, stages: string[]): Row[] {
  const stageIndex = new Map(
    stages.map((s, i) => [s.trim().toLowerCase(), i] as const),
  );

  const rows: Row[] = [];
  let row: Row | null = null;
  let cell: Cell | null = null;
  let stageIndent: number | null = null;

  source.split("\n").forEach((line, i) => {
    const lineNo = i + 1;
    if (!line.trim() || line.trim().startsWith("#")) return;

    const item = ITEM_RE.exec(line);
    if (!item) fail(lineNo, line, "expected a list item starting with `-`");
    const indent = item[1].replace(/\t/g, "  ").length;
    const text = item[2];

    if (indent === 0) {
      // Component
      let name = text;
      let anchor: Row["anchor"];
      const a = ANCHOR_RE.exec(name);
      if (a) {
        anchor = { x: parseFloat(a[1]), y: parseFloat(a[2]) };
        name = name.slice(0, a.index).trim();
      }
      row = {
        id: slugify(name),
        name,
        anchor,
        cells: stages.map(() => ({ mark: "empty" as Mark, details: [] })),
      };
      rows.push(row);
      cell = null;
      stageIndent = null;
      return;
    }

    if (!row) fail(lineNo, line, "indented item before any component");
    if (stageIndent === null) stageIndent = indent;

    if (indent <= stageIndent) {
      // Stage
      const { mark, label, note } = parseCheckbox(lineNo, line, text);
      const idx = stageIndex.get(label.toLowerCase());
      if (idx === undefined) {
        fail(
          lineNo,
          line,
          `unknown stage \`${label}\`, expected one of ${stages.join(", ")}`,
        );
      }
      cell = { mark, note, details: [] };
      row.cells[idx] = cell;
      return;
    }

    // Detail
    if (!cell) fail(lineNo, line, "detail item before any stage");
    const { mark, label, note } = parseCheckbox(lineNo, line, text);
    cell.details.push({ mark, text: note ? `${label}: ${note}` : label });
  });

  return rows;
}

// ---------------------------------------------------------------------------
// Dimensional plan: staged scopes, correlated with the status list by name.
//
//   - Stage 1: Dijkstra supports Leios     <- level 1: a release scope
//     - Generate BLS keys                  <- level 2: a scope item, matched by name
//       - Note or sub-item                 <- level 3: clarifications, shown muted
//
// The plan carries no marks of its own; status comes from the matching detail in
// the status list (or, for items that only have matching children, from those).

export type PlanItem = {
  name: string;
  children: string[];
};

export type PlanStage = {
  id: string;
  /** Full heading, e.g. "Stage 1: Dijkstra supports Leios". */
  title: string;
  /** Short prefix used as a chip elsewhere, e.g. "Stage 1". */
  label: string;
  items: PlanItem[];
};

export function parsePlan(source: string): PlanStage[] {
  const plan: PlanStage[] = [];
  let stage: PlanStage | null = null;
  let item: PlanItem | null = null;
  let itemIndent: number | null = null;

  source.split("\n").forEach((line, i) => {
    const lineNo = i + 1;
    if (!line.trim() || line.trim().startsWith("#")) return;

    const parsed = ITEM_RE.exec(line);
    if (!parsed) fail(lineNo, line, "expected a list item starting with `-`");
    const indent = parsed[1].replace(/\t/g, "  ").length;
    const text = parsed[2];

    if (indent === 0) {
      const title = text;
      stage = {
        id: slugify(title),
        title,
        label: title.split(":")[0].trim(),
        items: [],
      };
      plan.push(stage);
      item = null;
      itemIndent = null;
      return;
    }

    if (!stage) fail(lineNo, line, "indented item before any stage");
    if (itemIndent === null) itemIndent = indent;

    if (indent <= itemIndent) {
      item = { name: text, children: [] };
      stage.items.push(item);
      return;
    }

    if (!item) fail(lineNo, line, "sub-item before any scope item");
    item.children.push(text);
  });

  return plan;
}

export type ScopeRef = {
  componentId: string;
  componentName: string;
  mark: Mark;
  /** The owning component's mark in the assurance stage. */
  assurance: Mark;
};

/**
 * All details of the status list, keyed by name. Each reference also carries
 * the assurance mark of its component, since assurance is tracked per component
 * rather than per scope item.
 */
export function detailIndex(
  rows: Row[],
  stages: string[],
  assuranceStage: string = stages[stages.length - 1],
): Map<string, ScopeRef[]> {
  const assuranceIdx = stages.indexOf(assuranceStage);
  const index = new Map<string, ScopeRef[]>();
  rows.forEach((row) => {
    const assurance = row.cells[assuranceIdx]?.mark ?? "empty";
    row.cells.forEach((cell) => {
      cell.details.forEach((detail) => {
        const key = nameKey(detail.text);
        const refs = index.get(key) ?? [];
        refs.push({
          componentId: row.id,
          componentName: row.name,
          mark: detail.mark,
          assurance,
        });
        index.set(key, refs);
      });
    });
  });
  return index;
}

/** Roll several marks up into one: worst wins, all-done stays done. */
export function rollUp(marks: Mark[]): Mark {
  if (!marks.length) return "empty";
  if (marks.includes("missing")) return "missing";
  if (marks.includes("open")) return "open";
  if (marks.every((m) => m === "done")) return "done";
  if (marks.some((m) => m === "done" || m === "ongoing")) return "ongoing";
  return "empty";
}

export type CorrelatedItem = PlanItem & {
  refs: ScopeRef[];
  mark: Mark;
  /** Roll-up of the assurance marks of the components owning this item. */
  assurance: Mark;
  /** No detail in the status list matches this item, nor any of its children. */
  untracked: boolean;
};

export type CorrelatedStage = Omit<PlanStage, "items"> & {
  items: CorrelatedItem[];
};

/**
 * Match each plan item against the status list by name. Items that have no
 * direct match aggregate the status of their children, which covers grouping
 * items such as "Dijkstra block definition / serialization contains Leios".
 */
export function correlate(
  plan: PlanStage[],
  index: Map<string, ScopeRef[]>,
): CorrelatedStage[] {
  return plan.map((stage) => ({
    ...stage,
    items: stage.items.map((item) => {
      const direct = index.get(nameKey(item.name)) ?? [];
      const refs = direct.length
        ? direct
        : item.children.flatMap((c) => index.get(nameKey(c)) ?? []);
      return {
        ...item,
        refs,
        mark: rollUp(refs.map((r) => r.mark)),
        // One assurance vote per component, however many details it contributed.
        assurance: rollUp(
          refs
            .filter(
              (r, i) =>
                refs.findIndex((o) => o.componentId === r.componentId) === i,
            )
            .map((r) => r.assurance),
        ),
        untracked: refs.length === 0,
      };
    }),
  }));
}

/** Stage label per status detail name, e.g. "Double-buffered mempool" -> "Stage 3". */
export function stageLabels(plan: PlanStage[]): Map<string, string> {
  const labels = new Map<string, string>();
  plan.forEach((stage) => {
    stage.items.forEach((item) => {
      labels.set(nameKey(item.name), stage.label);
      item.children.forEach((c) => labels.set(nameKey(c), stage.label));
    });
  });
  return labels;
}
