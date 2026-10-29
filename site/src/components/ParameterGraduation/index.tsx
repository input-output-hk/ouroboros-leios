import { useColorMode } from "@docusaurus/theme-common";
import React, { useEffect, useMemo, useRef, useState } from "react";
import { DEFAULT_MODEL, evalPoint, needsInfo, refsKB } from "./deltaq";
import type { Model } from "./deltaq";
import type { GraduationScene, Scale, View } from "./scene";
import styles from "./styles.module.css";
import { statuses } from "./types";
import type { Plan, Plans, Status, Step } from "./types";

export type { Plan, Plans, Step } from "./types";

const F = 0.05;

const MODEL_FIELDS: [keyof Model, string, number][] = [
  ["seats", "committee seats", 50],
  ["pc", "target P(C)", 0.01],
  ["pf", "target F_full|C", 0.001],
  ["beta", "active adversary β", 0.05],
  ["tau", "quorum τ", 0.01],
  ["c", "Plutus ms per G steps", 0.1],
  ["fexec", "steps run by voters", 0.05],
  ["h", "L_hdr (ms)", 100],
  ["refsCap", "EB refs cap (kB)", 50],
];

const VALIDATION_FIELDS: [keyof Model, string, number][] = [
  ["miss", "missed txs π₁", 0.01],
  ["txBytes", "avg tx size (B)", 50],
  ["applyMs", "applyTx ms/tx", 0.01],
  ["applySd", "applyTx sd ms", 0.01],
  ["reapplyMs", "reapplyTx ms/tx", 0.01],
  ["reapplySd", "reapplyTx sd ms", 0.01],
];

const VIEW_LABELS: [View, string][] = [
  ["iso", "3D"],
  ["top", "Top: size × Plutus"],
  ["front", "Front: size × timing"],
  ["side", "Side: Plutus × timing"],
];

const STATUS_LABEL: Record<Status, string> = { done: "✓", current: "●", planned: "" };
const STATUS_TITLE: Record<Status, string> = { done: "Accomplished", current: "Current", planned: "Planned" };

const fmt = (v: number) => (Math.round(v * 10) / 10).toFixed(1);
const trim = (x: number) => x.toFixed(2).replace(/\.?0+$/, "");
const pct = (v: number) =>
  v >= 0.9999 ? ">99.99%" : v >= 0.99 ? (100 * v).toFixed(2) + "%" : v >= 0.01 ? (100 * v).toFixed(1) + "%" : "<1%";
const fmtB = (v: number) => (v >= 1e6 ? (v / 1e6).toFixed(v % 1e6 ? 2 : 0) + " MB" : Math.round(v / 1000) + " kB");
const fmtU = (v: number) => (v >= 1e12 ? trim(v / 1e12) + "T" : v >= 1e9 ? trim(v / 1e9) + "G" : trim(v / 1e6) + "M");
const kb = (v: number) => Math.round(v / 1000).toLocaleString("en-US");
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));

function Seg<T extends string>({ value, options, onChange, label }: { value: T; options: [T, string][]; onChange: (v: T) => void; label: string }) {
  return (
    <div className={styles.seg} role="group" aria-label={label}>
      {options.map(([v, l]) => (
        <button key={v} type="button" aria-pressed={v === value} onClick={() => onChange(v)}>
          {l}
        </button>
      ))}
    </div>
  );
}

export interface ParameterGraduationProps {
  plans: Plans;
  model?: Partial<Model>;
}

export default function ParameterGraduation({ plans: initialPlans, model: initialModel }: ParameterGraduationProps): React.ReactElement {
  const defaults = useMemo(() => ({ plans: clone(initialPlans), model: { ...DEFAULT_MODEL, ...initialModel } }), [initialPlans, initialModel]);
  const [plans, setPlans] = useState<Plans>(() => clone(defaults.plans));
  const [active, setActive] = useState<string>(() => Object.keys(initialPlans)[0]);
  const [model, setModel] = useState<Model>(defaults.model);
  const [showSurface, setShowSurface] = useState(true);
  const [scale, setScale] = useState<Scale>("log");
  const [view, setView] = useState<View>("iso");
  // Bumped on structural changes so the uncontrolled inputs pick up new values.
  const [version, setVersion] = useState(0);
  const [sceneReady, setSceneReady] = useState(false);

  const stageRef = useRef<HTMLDivElement>(null);
  const labelsRef = useRef<HTMLDivElement>(null);
  const rootRef = useRef<HTMLDivElement>(null);
  const sceneRef = useRef<GraduationScene | null>(null);
  const { colorMode } = useColorMode();

  const plan: Plan = plans[active];
  const status = useMemo(() => statuses(plan), [plan]);
  const hdr = model.h / 1000;

  useEffect(() => {
    let live = true;
    import("./scene").then(({ GraduationScene }) => {
      if (!live || !stageRef.current || !labelsRef.current || !rootRef.current) return;
      sceneRef.current = new GraduationScene(stageRef.current, labelsRef.current, rootRef.current, {
        lbl: styles.lbl,
        axis: styles.axis,
        set: styles.set,
        cnt: styles.cnt,
        tick: styles.tick,
        done: styles.done,
      });
      setSceneReady(true);
    });
    return () => {
      live = false;
      sceneRef.current?.dispose();
      sceneRef.current = null;
    };
  }, []);

  useEffect(() => {
    if (!sceneReady) return;
    sceneRef.current?.update({
      steps: plan.steps,
      status,
      planColor: `--pg-${plan.color}`,
      hdr,
      refsCap: model.refsCap,
      scale,
      showSurface,
      needsInfo: (B, S) => needsInfo(model, B, S),
    });
  }, [sceneReady, plan, status, model, hdr, scale, showSurface]);

  useEffect(() => {
    sceneRef.current?.retheme();
  }, [colorMode]);

  const rows = useMemo(
    () => plan.steps.map((p) => ({ e: evalPoint(model, p.txs, p.steps, p.diff) })),
    [plan, model],
  );

  const editPlan = (f: (p: Plan) => void, structural = false) => {
    setPlans((ps) => {
      const next = clone(ps);
      f(next[active]);
      return next;
    });
    if (structural) setVersion((v) => v + 1);
  };
  const editStep = (i: number, k: "id" | "txs" | "steps" | "diff", raw: string) => {
    if (k === "id") return editPlan((p) => void (p.steps[i].id = raw.trim() || "?"));
    const v = parseFloat(raw);
    if (!isFinite(v) || v <= 0) return;
    editPlan((p) => void (p.steps[i][k] = v));
  };
  const fieldGrid = (name: string, fields: [keyof Model, string, number][]) => (
    <div className={styles.model} key={`${name}-${version}`}>
      {fields.map(([k, label, step]) => (
        <label key={k}>
          <span>{label}</span>
          <input
            type="number"
            step={step}
            defaultValue={model[k] as number}
            aria-label={label}
            onChange={(e) => {
              const v = parseFloat(e.target.value);
              if (isFinite(v)) setModel((m) => ({ ...m, [k]: v }));
            }}
          />
        </label>
      ))}
    </div>
  );
  const changeView = (v: View) => {
    setView(v);
    sceneRef.current?.setView(v);
  };

  return (
    <div className={styles.root} ref={rootRef}>
      <div className={styles.app}>
        <div className={styles.stage} ref={stageRef}>
          <div className={styles.labels} ref={labelsRef} />
          <div className={styles.overlay}>
            <h3>{plan.title}</h3>
            <p>
              Drag to rotate, scroll or pinch to zoom, right-drag to pan. The surface is an indicative minimum L_diff from the
              uncalibrated model. <span className={styles.legendDone}>✓</span> accomplished,{" "}
              <span className={styles.legendCurrent}>●</span> current, dashed path ahead.
            </p>
          </div>
          <div className={styles.warn} role="note">
            <b>Preliminary.</b> The DeltaQ model is not calibrated against testnet data: compare steps, don’t read the timings as
            requirements.
          </div>
          <div className={styles.views} role="group" aria-label="Camera presets">
            {VIEW_LABELS.map(([v, l]) => (
              <button key={v} type="button" aria-pressed={view === v} onClick={() => changeView(v)}>
                {l}
              </button>
            ))}
            <button type="button" aria-pressed={showSurface} onClick={() => setShowSurface((s) => !s)}>
              Surface
            </button>
            <button type="button" aria-pressed={scale === "log"} onClick={() => setScale((s) => (s === "log" ? "linear" : "log"))}>
              Log scale
            </button>
          </div>
        </div>
        <aside className={styles.side}>
          <section>
            <div className={styles.head}>
              <h3>Plan</h3>
              <Seg
                label="Plan"
                value={active}
                options={Object.entries(plans).map(([k, p]) => [k, p.name])}
                onChange={(k) => {
                  setActive(k);
                  setVersion((v) => v + 1);
                }}
              />
            </div>
            <div className={styles.wrap}>
              <table className={styles.table} key={`${active}-${version}`}>
                <thead>
                  <tr>
                    <th title="Current step on the network">Now</th>
                    <th>Step</th>
                    <th>EB txs kB</th>
                    <th>Steps G</th>
                    <th>L_diff s</th>
                    <th>P(C)</th>
                    <th>F|C</th>
                    <th>Opp.</th>
                    <th />
                  </tr>
                </thead>
                <tbody>
                  {plan.steps.map((p, i) => {
                    const r = rows[i];
                    const st = status[i];
                    return (
                      <tr key={i} className={styles[`row_${st}`]}>
                        <td title={STATUS_TITLE[st]}>
                          <label className={styles.status}>
                            <input
                              type="radio"
                              name={`current-${active}`}
                              checked={st === "current"}
                              onChange={() => editPlan((pl) => void (pl.current = p.id))}
                              aria-label={`Mark ${p.id} as current`}
                            />
                            <span>{STATUS_LABEL[st]}</span>
                          </label>
                        </td>
                        <td className={styles.name} style={{ "--c": `var(--pg-${p.color ?? plan.color})` } as React.CSSProperties}>
                          <i />
                          <input type="text" defaultValue={p.id} aria-label="Step name" onChange={(e) => editStep(i, "id", e.target.value)} />
                        </td>
                        <td>
                          <input type="number" min={100} max={12000} step={10} defaultValue={p.txs} aria-label={`${p.id} EB txs kB`} onChange={(e) => editStep(i, "txs", e.target.value)} />
                        </td>
                        <td>
                          <input type="number" min={100} max={2000} step={10} defaultValue={p.steps} aria-label={`${p.id} steps G`} onChange={(e) => editStep(i, "steps", e.target.value)} />
                        </td>
                        <td>
                          <input type="number" min={3.1} max={17} step={0.1} defaultValue={p.diff} aria-label={`${p.id} L_diff s`} onChange={(e) => editStep(i, "diff", e.target.value)} />
                        </td>
                        <td>{r && <span className={r.e.pc >= model.pc ? "" : styles.bad}>{pct(r.e.pc)}</span>}</td>
                        <td>{r && <span className={r.e.F >= model.pf ? "" : styles.bad}>{pct(r.e.F)}</span>}</td>
                        <td>{Math.round(100 * Math.exp(-F * 2 * p.diff))}%</td>
                        <td>
                          <button
                            type="button"
                            className={styles.rm}
                            disabled={plan.steps.length < 2}
                            aria-label={`Remove ${p.id}`}
                            onClick={() => editPlan((pl) => void pl.steps.splice(i, 1), true)}
                          >
                            ×
                          </button>
                        </td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            </div>

            <div className={styles.head}>
              <h3>Derived protocol parameters</h3>
            </div>
            <div className={styles.wrap}>
              <table className={styles.table}>
                <thead>
                  <tr>
                    <th>Step</th>
                    <th>L_hdr s</th>
                    <th>L_vote s</th>
                    <th>L_diff s</th>
                    <th>EB refs kB</th>
                    <th>EB txs kB</th>
                    <th>Plutus mem</th>
                    <th>Plutus steps</th>
                    <th>Ref scripts</th>
                  </tr>
                </thead>
                <tbody>
                  {plan.steps.map((p, i) => {
                    const B = p.txs * 1000;
                    const S = p.steps * 1e9;
                    return (
                      <tr key={i} className={styles[`row_${status[i]}`]}>
                        <td className={styles.name} style={{ "--c": `var(--pg-${p.color ?? plan.color})` } as React.CSSProperties}>
                          <i />
                          {p.id}
                        </td>
                        <td>{fmt(hdr)}</td>
                        <td className={p.diff - 3 * hdr > 0 ? "" : styles.bad}>{fmt(p.diff - 3 * hdr)}</td>
                        <td>
                          <b>{fmt(p.diff)}</b>
                        </td>
                        <td>{kb(refsKB(model, p.txs) * 1000)}</td>
                        <td>
                          <b>{kb(B)}</b>
                        </td>
                        <td>{fmtU(S * 0.0036)}</td>
                        <td>
                          <b>{fmtU(S)}</b>
                        </td>
                        <td>{fmtB(p.steps * 20000)}</td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            </div>
          </section>

          <section>
            <div className={styles.head}>
              <h3>Model: DeltaQ</h3>
              <Seg label="TCP model" value={model.net} options={[["mathis", "Mathis (Reno)"], ["cubic", "CUBIC"]]} onChange={(net) => setModel((m) => ({ ...m, net }))} />
            </div>
            {fieldGrid("model", MODEL_FIELDS)}
            <div className={styles.head}>
              <h3>Validation</h3>
            </div>
            {fieldGrid("validation", VALIDATION_FIELDS)}
          </section>
        </aside>
      </div>
    </div>
  );
}
