import { useColorMode } from "@docusaurus/theme-common";
import useBaseUrl from "@docusaurus/useBaseUrl";
import React, { useEffect, useMemo, useRef, useState } from "react";
import { DEFAULT_MODEL, VSPAN, evalPoint, makeDQ, needsInfo } from "./deltaq";
import type { DQ, Model } from "./deltaq";
import type { GraduationScene, View } from "./scene";
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

// Outbound: the first milestone, then per milestone pair (A, B): (B.txs, A.steps) and B, all on one L_diff plane.
// Return: directly back through the milestones at the minimum L_diff plus a margin, rounded up to 0.1 s.
function generate(ms: Step[], g: { plane: number; margin: number; prefix: string }, need: (B: number, S: number) => number, ymax: number): Step[] {
  const at = (a: Step, b: Step) => ({ id: "", txs: a.txs, steps: b.steps, diff: g.plane });
  const up = [at(ms[0], ms[0])];
  for (let i = 1; i < ms.length; i++) up.push(at(ms[i], ms[i - 1]), at(ms[i], ms[i]));
  const down = ms
    .slice()
    .reverse()
    .map((m) => {
      const n = need(m.txs, m.steps);
      return { id: "", txs: m.txs, steps: m.steps, diff: n === Infinity ? ymax : Math.ceil((n + g.margin) * 10 - 1e-9) / 10 };
    });
  return up.concat(down).map((p, i) => ({ ...p, id: g.prefix + (i + 1) }));
}

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
  const [view, setView] = useState<View>("iso");
  // Bumped on structural changes so the uncontrolled inputs pick up new values.
  const [version, setVersion] = useState(0);
  const [out, setOut] = useState<string | null>(null);
  const [dq, setDq] = useState<DQ | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [sceneReady, setSceneReady] = useState(false);

  const stageRef = useRef<HTMLDivElement>(null);
  const labelsRef = useRef<HTMLDivElement>(null);
  const rootRef = useRef<HTMLDivElement>(null);
  const sceneRef = useRef<GraduationScene | null>(null);
  const { colorMode } = useColorMode();
  const dataUrl = useBaseUrl("/data/parameter-graduation-deltaq.json");

  const plan: Plan = plans[active];
  const status = useMemo(() => statuses(plan), [plan]);
  const hdr = model.h / 1000;
  const ymax = 3 * hdr + VSPAN;

  useEffect(() => {
    let live = true;
    fetch(dataUrl)
      .then((r) => (r.ok ? r.json() : Promise.reject(new Error(r.statusText))))
      .then((s) => live && setDq(makeDQ(s)))
      .catch((e) => live && setError(String(e.message || e)));
    return () => {
      live = false;
    };
  }, [dataUrl]);

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
        current: styles.current,
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
    if (!sceneReady || !dq) return;
    sceneRef.current?.update({
      steps: plan.steps,
      status,
      planColor: `--pg-${plan.color}`,
      hdr,
      showSurface,
      needsInfo: (B, S) => needsInfo(dq, model, B, S),
    });
  }, [sceneReady, dq, plan, status, model, hdr, showSurface]);

  useEffect(() => {
    sceneRef.current?.retheme();
  }, [colorMode]);

  const rows = useMemo(
    () =>
      dq
        ? plan.steps.map((p) => ({ ni: needsInfo(dq, model, p.txs, p.steps), e: evalPoint(dq, model, p.txs, p.steps, p.diff) }))
        : null,
    [dq, plan, model],
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
  const regenerate = () => {
    const g = plan.generate;
    const from = g && plans[g.from];
    if (!g || !from || !dq) return;
    editPlan((p) => {
      p.steps = generate(from.steps, g, (B, S) => needsInfo(dq, model, B, S).need, ymax);
    }, true);
  };
  const reset = () => {
    setPlans(clone(defaults.plans));
    setModel(defaults.model);
    setVersion((v) => v + 1);
    changeView("iso");
  };
  const changeView = (v: View) => {
    setView(v);
    sceneRef.current?.setView(v);
  };
  const copy = async (text: string) => {
    setOut(text);
    try {
      await navigator.clipboard.writeText(text);
    } catch (_) {
      // The text stays visible below for manual copying.
    }
  };
  const copyTsv = () =>
    copy(
      "# plan     step  txs_B     steps_G  diff_ms\n" +
        Object.entries(plans)
          .map(([k, pl]) =>
            pl.steps
              .map(
                (p) =>
                  `${k.padEnd(8)} ${p.id.padEnd(5)} ${String(Math.round(p.txs * 1000)).padEnd(9)} ${String(p.steps).padEnd(8)} ${Math.round(p.diff * 1000)}`,
              )
              .join("\n"),
          )
          .join("\n") +
        "\n",
    );

  return (
    <div className={styles.root} ref={rootRef}>
      <div className={styles.stage} ref={stageRef}>
        <div className={styles.labels} ref={labelsRef} />
        <div className={styles.overlay}>
          <h3>{plan.title}</h3>
          {!dq && <p>{error ? `Could not load the DeltaQ model: ${error}` : "Loading the DeltaQ model…"}</p>}
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
        </div>
      </div>
      <p className={styles.note}>
        Drag to rotate, scroll or pinch to zoom, right-drag to pan. The surface is the minimum L_diff each point needs; a step
        above it is feasible. <span className={styles.legendDone}>✓</span> accomplished, <span className={styles.legendCurrent}>●</span>{" "}
        current, dashed path ahead.
      </p>

      <div className={styles.panels}>
        <section>
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
          <div className={styles.wrap}>
            <table className={styles.table} key={`${active}-${version}`}>
              <thead>
                <tr>
                  <th title="Current step on the network">Now</th>
                  <th>Step</th>
                  <th>EB txs kB</th>
                  <th>Steps G</th>
                  <th>L_diff s</th>
                  <th>Needs</th>
                  <th>P(C)</th>
                  <th>F|C</th>
                  <th>Opp.</th>
                  <th />
                </tr>
              </thead>
              <tbody>
                {plan.steps.map((p, i) => {
                  const r = rows?.[i];
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
                      <td className={styles.need}>
                        {r && (
                          <>
                            <span className={p.diff >= r.ni.need ? styles.ok : styles.bad}>
                              {r.ni.need === Infinity ? "> " + trim(ymax) : fmt(r.ni.need)}
                            </span>
                            <small>{r.ni.bind}</small>
                          </>
                        )}
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
          {plan.generate && (
            <div className={styles.gen} key={`gen-${active}-${version}`}>
              <label>
                Outbound L_diff{" "}
                <input type="number" min={3.1} max={17} step={0.5} defaultValue={plan.generate.plane}
                  onChange={(e) => { const v = parseFloat(e.target.value); if (isFinite(v)) editPlan((p) => void (p.generate!.plane = v)); }} />{" "}
                s
              </label>
              <label>
                Return margin{" "}
                <input type="number" min={0} max={5} step={0.1} defaultValue={plan.generate.margin}
                  onChange={(e) => { const v = parseFloat(e.target.value); if (isFinite(v) && v >= 0) editPlan((p) => void (p.generate!.margin = v)); }} />{" "}
                s
              </label>
              <button type="button" onClick={regenerate} disabled={!dq}>
                Regenerate from {plans[plan.generate.from]?.name ?? plan.generate.from}
              </button>
            </div>
          )}
          <div className={styles.row}>
            <button
              type="button"
              onClick={() =>
                editPlan((pl) => {
                  const last = pl.steps[pl.steps.length - 1];
                  pl.steps.push({ id: "new", txs: last.txs, steps: last.steps, diff: last.diff });
                }, true)
              }
            >
              Add step
            </button>
            <button type="button" onClick={() => editPlan((pl) => void delete pl.current)}>
              Clear current
            </button>
          </div>
          <p className={styles.note}>
            Needs: minimum L_diff from the model. With L_vote = L_diff − 3·L_hdr, the certification gate is W = 3·L_hdr + L_vote +
            L_diff = 2·L_diff. Opportunity = exp(−f·W) with f = 0.05 per second. Edits here are not saved; copy the plans and paste
            them into the page source to keep them.
          </p>

          <h3>Derived protocol parameters</h3>
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
                      <td>{kb((B * 40) / 260)}</td>
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
          <p className={styles.note}>
            L_hdr fixed; L_vote = L_diff − 3·L_hdr. EB references = EB txs × 40/260. Plutus memory = Plutus steps × 0.0036. Reference
            scripts = 20 kB per G steps (4 MB at 200G). Bold: leading values.
          </p>
        </section>

        <section>
          <h3>Model: DeltaQ</h3>
          <Seg label="TCP model" value={model.net} options={[["mathis", "Mathis (Reno)"], ["cubic", "CUBIC"]]} onChange={(net) => setModel((m) => ({ ...m, net }))} />
          <Seg
            label="EB references fetch"
            value={model.body}
            options={[["plan", "EB refs: plan limit"], ["report", "EB refs: report’s 1–512 kB mix"]]}
            onChange={(body) => setModel((m) => ({ ...m, body }))}
          />
          <div className={styles.model} key={`model-${version}`}>
            {MODEL_FIELDS.map(([k, label, step]) => (
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
          <p className={styles.note}>
            Needs is the smallest L_diff with P(C) ≥ target at t_v = 3·L_hdr + L_vote = L_diff, and F_full|C ≥ target at W = 2·L_diff.
            Sampled from the{" "}
            <a href="https://github.com/input-output-hk/ouroboros-leios/blob/yveshauser/conditional-certification-diffusion-numerical-report/docs/conditional-certification-diffusion.md">
              conditional certification diffusion model
            </a>{" "}
            (analysis.py on that branch): voter law G = EB references (multi-hop) ⊗ missing txs (1 hop, π1 = 1/6) ⊗ validation CPU;
            reapply-only law for the all-nodes term; top-stake committee of the configured seat count (900: coverage ≈ 98.84%) over a
            synthetic 2,500-node stake distribution, Normal approximation. “Plan limit” fetches EB references at the plan’s limit,
            EB txs × 40/260. “Report’s mix” keeps the model’s fixed 1/64/256/512 kB body for every size and reproduces the report’s
            tables to within 0.05 s. Voters additionally spend c · steps · f_exec on Plutus execution. Node timings are treated as
            independent.
          </p>

          <h3>Export</h3>
          <div className={styles.row}>
            <button type="button" onClick={() => copy(JSON.stringify(plans, null, 2))}>
              Copy plans
            </button>
            <button type="button" onClick={copyTsv}>
              Copy plan3d.tsv
            </button>
            <button
              type="button"
              onClick={() =>
                copy("# DeltaQ planning settings\n# name    value\n" + Object.entries(model).map(([k, v]) => `${k.padEnd(8)} ${v}`).join("\n") + "\n")
              }
            >
              Copy model
            </button>
            <button type="button" onClick={reset}>
              Reset
            </button>
          </div>
          {out != null && <pre className={styles.out}>{out}</pre>}
        </section>
      </div>
    </div>
  );
}
