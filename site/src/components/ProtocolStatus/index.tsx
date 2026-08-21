import React, { useState } from "react";
import useBaseUrl from "@docusaurus/useBaseUrl";
import styles from "./styles.module.css";
import {
  Cell,
  Mark,
  Row,
  correlate,
  detailIndex,
  nameKey,
  parsePlan,
  parseStatus,
  stageLabels,
} from "./parse";

export { parseStatus, parsePlan } from "./parse";
export type { Mark, Row, PlanStage } from "./parse";

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

function Pip({ mark }: { mark: Mark }) {
  return (
    <span className={`${styles.pip} ${styles[`pip_${mark}`]}`}>
      {MARK_SYMBOL[mark]}
    </span>
  );
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

function CellDetails({
  cell,
  labels,
}: {
  cell: Cell;
  labels: Map<string, string>;
}) {
  if (!cell.details.length) return null;
  return (
    <ul className={styles.details}>
      {cell.details.map((d, i) => {
        const label = labels.get(nameKey(d.text));
        return (
          <li key={i}>
            <span
              className={`${styles.detailPip} ${styles[`dot_${d.mark}`]}`}
            />
            <span>
              {label && <span className={styles.stageChip}>{label}</span>}
              {d.text}
            </span>
          </li>
        );
      })}
    </ul>
  );
}

function StatusTable({
  row,
  stages,
  labels,
}: {
  row: Row;
  stages: string[];
  labels: Map<string, string>;
}) {
  return (
    <table className={styles.tooltipTable}>
      <tbody>
        {stages.map((stage, i) => {
          const cell = row.cells[i];
          return (
            <tr key={stage}>
              <th>{stage}</th>
              <td>
                <Pip mark={cell.mark} />
                <span className={styles.markText}>
                  {cell.note ?? MARK_LABEL[cell.mark]}
                </span>
                <CellDetails cell={cell} labels={labels} />
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
  labels,
  style,
  open,
  onToggle,
}: {
  row: Row;
  stages: string[];
  labels: Map<string, string>;
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
        <StatusTable row={row} stages={stages} labels={labels} />
      </div>
    </div>
  );
}

export default function ProtocolStatus({
  stages,
  source,
  plan,
}: {
  stages: string[];
  source: string;
  /** Optional dimensional plan; adds a stage chip to matching details. */
  plan?: string;
}): JSX.Element {
  const svgUrl = useBaseUrl("/img/leios-protocol-flow.svg");
  const [openId, setOpenId] = useState<string | null>(null);

  const rows = parseStatus(source, stages);
  const labels = plan
    ? stageLabels(parsePlan(plan))
    : new Map<string, string>();
  const anchored = rows.filter((r) => r.anchor);
  const crossCutting = rows.filter((r) => !r.anchor);

  return (
    <div className={styles.root}>
      <div className={styles.legend}>
        {(["done", "ongoing", "open", "empty"] as Mark[]).map((m) => (
          <span key={m} className={styles.legendItem}>
            <Pip mark={m} />
            <span>{MARK_LABEL[m]}</span>
          </span>
        ))}
      </div>
      <br />
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
              labels={labels}
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
                labels={labels}
                open={openId === row.id}
                onToggle={() => setOpenId(openId === row.id ? null : row.id)}
              />
            ))}
          </div>
        </div>
      )}
    </div>
  );
}

/**
 * One table per stage of the dimensional plan. The plan itself carries no
 * marks; each item's status is looked up in the status list by name.
 */
export function ReleaseStages({
  stages,
  source,
  plan,
}: {
  stages: string[];
  source: string;
  plan: string;
}): JSX.Element {
  // Assurance is tracked per component, in the last stage column.
  const assuranceStage = stages[stages.length - 1];
  const index = detailIndex(
    parseStatus(source, stages),
    stages,
    assuranceStage,
  );
  const correlated = correlate(parsePlan(plan), index);

  return (
    <>
      {correlated.map((stage) => {
        const tracked = stage.items.filter((i) => !i.untracked);
        const done = tracked.filter((i) => i.mark === "done").length;
        return (
          <div key={stage.id} className={styles.stageBlock}>
            <h3 id={stage.id} className={styles.stageTitle}>
              {stage.title}
              <span className={styles.stageCount}>
                {done}/{stage.items.length} done
              </span>
            </h3>
            <div className={styles.matrixWrap}>
              <table className={styles.matrix}>
                <thead>
                  <tr>
                    <th>Scope item</th>
                    <th>Component</th>
                    <th>Implementation</th>
                    <th>{assuranceStage}</th>
                  </tr>
                </thead>
                <tbody>
                  {stage.items.map((item) => (
                    <tr key={item.name}>
                      <td className={styles.scopeCell}>
                        {item.name}
                        {item.children.length > 0 && (
                          <ul className={styles.details}>
                            {item.children.map((c) => (
                              <li key={c}>{c}</li>
                            ))}
                          </ul>
                        )}
                      </td>
                      <td>
                        {item.untracked ? (
                          <span className={styles.untracked}>
                            not in status list
                          </span>
                        ) : (
                          item.refs
                            .map((r) => r.componentName)
                            .filter((n, i, all) => all.indexOf(n) === i)
                            .join(", ")
                        )}
                      </td>
                      <td title={MARK_LABEL[item.mark]}>
                        {!item.untracked && <Pip mark={item.mark} />}
                        <span className={styles.markText}>
                          {item.untracked ? "–" : MARK_LABEL[item.mark]}
                        </span>
                      </td>
                      <td title={MARK_LABEL[item.assurance]}>
                        {!item.untracked && <Pip mark={item.assurance} />}
                        <span className={styles.markText}>
                          {item.untracked ? "–" : MARK_LABEL[item.assurance]}
                        </span>
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        );
      })}
    </>
  );
}

/** The same data rendered as a full component × stage matrix. */
export function ProtocolMatrix({
  stages,
  source,
}: {
  stages: string[];
  source: string;
}): JSX.Element {
  const rows = parseStatus(source, stages);
  return (
    <div className={styles.matrixWrap}>
      <table className={styles.matrix}>
        <thead>
          <tr>
            <th>Component</th>
            {stages.map((s) => (
              <th key={s}>{s}</th>
            ))}
          </tr>
        </thead>
        <tbody>
          {rows.map((row) => (
            <tr key={row.id}>
              <th scope="row">{row.name}</th>
              {row.cells.map((cell, i) => (
                <td key={i} title={cell.note ?? MARK_LABEL[cell.mark]}>
                  <Pip mark={cell.mark} />
                  {cell.note && (
                    <span className={styles.matrixNote}>{cell.note}</span>
                  )}
                </td>
              ))}
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}
