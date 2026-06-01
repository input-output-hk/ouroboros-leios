import React, { useState } from "react";
import useBaseUrl from "@docusaurus/useBaseUrl";
import styles from "./styles.module.css";

type Mark = "done" | "ongoing" | "missing" | "open" | "empty";

type Cell = {
  mark: Mark;
  note?: string;
};

export type RawRow = {
  id: string;
  name: string;
  cells: Record<string, { mark: Mark; note?: string }>;
  anchor?: { x: number; y: number };
};

type Row = {
  id: string;
  name: string;
  anchor?: { x: number; y: number };
  cells: Cell[]; // aligned with the stages prop
};

const MARK_LABEL: Record<Mark, string> = {
  done: "Done",
  ongoing: "Ongoing",
  missing: "Missing",
  open: "Open question",
  empty: "Not started",
};

const MARK_SYMBOL: Record<Mark, string> = {
  done: "✓",
  ongoing: "~",
  missing: "–",
  open: "?",
  empty: "",
};

const VIEWBOX_W = 1120.77;
const VIEWBOX_H = 471.62;

function progressFraction(row: Row): number {
  // Weighted progress across all stages: done = 1, ongoing = 0.5, else 0.
  const weighted = row.cells.map((c) => {
    if (c.mark === "done") return 1;
    if (c.mark === "ongoing") return 0.5;
    return 0;
  });
  return weighted.reduce((a, b) => a + b, 0) / weighted.length;
}

// Color of the filled portion: the worst non-empty mark present.
// Priority (worst first): missing > open > ongoing > done.
const WORST_ORDER: Mark[] = ["missing", "open", "ongoing", "done"];

function worstMark(row: Row): Mark {
  for (const m of WORST_ORDER) {
    if (row.cells.some((c) => c.mark === m)) return m;
  }
  return "done";
}

function StatusDots({ row }: { row: Row }) {
  return (
    <span className={styles.dots} aria-hidden="true">
      {row.cells.map((cell, i) => (
        <span
          key={i}
          className={`${styles.dot} ${styles[`dot_${cell.mark}`]}`}
        />
      ))}
    </span>
  );
}

function StatusTable({ row, stages }: { row: Row; stages: string[] }) {
  return (
    <table className={styles.tooltipTable}>
      <tbody>
        {stages.map((stage, i) => {
          const cell = row.cells[i];
          return (
            <tr key={stage}>
              <th>{stage}</th>
              <td>
                <span className={`${styles.pip} ${styles[`pip_${cell.mark}`]}`}>
                  {MARK_SYMBOL[cell.mark]}
                </span>
                <span className={styles.markText}>
                  {cell.note ?? MARK_LABEL[cell.mark]}
                </span>
              </td>
            </tr>
          );
        })}
      </tbody>
    </table>
  );
}

function Widget({
  row,
  stages,
  style,
  open,
  onToggle,
}: {
  row: Row;
  stages: string[];
  style?: React.CSSProperties;
  open: boolean;
  onToggle: () => void;
}) {
  const worst = worstMark(row);
  const pct = Math.round(progressFraction(row) * 100);
  return (
    <div
      className={`${styles.widget} ${open ? styles.widgetOpen : ""}`}
      style={style}
    >
      <button
        type="button"
        className={styles.widgetButton}
        onClick={onToggle}
        aria-expanded={open}
        aria-label={row.name}
      >
        <span
          className={`${styles.ring} ${styles[`ring_${worst}`]}`}
          style={{ "--pct": `${pct}` } as React.CSSProperties}
          aria-hidden="true"
        >
          <span className={styles.ringInner} />
        </span>
        <span className={styles.widgetBody}>
          <span className={styles.widgetName}>{row.name}</span>
          <StatusDots row={row} />
        </span>
      </button>
      <div className={styles.tooltip} role="dialog">
        <div className={styles.tooltipTitle}>{row.name}</div>
        <StatusTable row={row} stages={stages} />
      </div>
    </div>
  );
}

export default function ProtocolStatus({
  stages,
  rows,
}: {
  stages: string[];
  rows: RawRow[];
}): JSX.Element {
  const svgUrl = useBaseUrl("/img/leios-protocol-flow.svg");
  const [openId, setOpenId] = useState<string | null>(null);

  const normalized: Row[] = rows.map((r) => ({
    id: r.id,
    name: r.name,
    anchor: r.anchor,
    cells: stages.map((s) => r.cells[s] ?? { mark: "empty" as Mark }),
  }));
  const anchored = normalized.filter((r) => r.anchor);
  const crossCutting = normalized.filter((r) => !r.anchor);

  return (
    <div className={styles.root}>
      <div
        className={styles.diagramWrap}
        style={{ aspectRatio: `${VIEWBOX_W} / ${VIEWBOX_H}` }}
      >
        <img
          src={svgUrl}
          alt="Leios protocol flow diagram"
          className={styles.diagram}
          loading="eager"
        />
        {anchored.map((row) => {
          const left = `${(row.anchor!.x / VIEWBOX_W) * 100}%`;
          const top = `${(row.anchor!.y / VIEWBOX_H) * 100}%`;
          return (
            <Widget
              key={row.id}
              row={row}
              stages={stages}
              style={{ left, top }}
              open={openId === row.id}
              onToggle={() => setOpenId(openId === row.id ? null : row.id)}
            />
          );
        })}
      </div>

      {crossCutting.length > 0 && (
        <div className={styles.crossCutting}>
          <h3 className={styles.sectionTitle}>Cross-cutting components</h3>
          <div className={styles.crossGrid}>
            {crossCutting.map((row) => (
              <Widget
                key={row.id}
                row={row}
                stages={stages}
                open={openId === row.id}
                onToggle={() => setOpenId(openId === row.id ? null : row.id)}
              />
            ))}
          </div>
        </div>
      )}

      <div className={styles.legend}>
        {(["done", "ongoing", "open", "empty"] as Mark[]).map((m) => (
          <span key={m} className={styles.legendItem}>
            <span className={`${styles.pip} ${styles[`pip_${m}`]}`}>
              {MARK_SYMBOL[m]}
            </span>
            <span>{MARK_LABEL[m]}</span>
          </span>
        ))}
      </div>
    </div>
  );
}
