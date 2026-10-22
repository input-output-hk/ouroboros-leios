import * as THREE from "three";
import { OrbitControls } from "three/examples/jsm/controls/OrbitControls.js";
import { VSPAN } from "./deltaq";
import type { Binding } from "./deltaq";
import type { Status, Step } from "./types";

export type View = "iso" | "top" | "front" | "side";

export interface SceneInput {
  steps: Step[];
  status: Status[];
  planColor: string;
  // L_hdr in seconds.
  hdr: number;
  showSurface: boolean;
  needsInfo: (B: number, S: number) => { need: number; bind: Binding };
}

export interface LabelClasses {
  lbl: string;
  axis: string;
  set: string;
  cnt: string;
  tick: string;
  done: string;
  current: string;
}

// EB txs kB and Plutus steps G; L_diff spans 3·L_hdr .. 3·L_hdr + VSPAN.
const RANGE = { x: [100, 12000], z: [100, 2000] };
const SPAN = 10;
const YSCALE = 0.55;
const YTOP = VSPAN * YSCALE;
const XT = [100, 200, 500, 1000, 2000, 5000, 10000];
const ZT = [100, 200, 500, 1000, 2000];

const lg = Math.log10;
const sx = (B: number) => ((lg(B) - lg(RANGE.x[0])) / (lg(RANGE.x[1]) - lg(RANGE.x[0]))) * SPAN;
// Larger steps recede.
const sz = (S: number) => SPAN - ((lg(S) - lg(RANGE.z[0])) / (lg(RANGE.z[1]) - lg(RANGE.z[0]))) * SPAN;

export const fmt = (v: number) => (Math.round(v * 10) / 10).toFixed(1);
export const trim = (x: number) => x.toFixed(2).replace(/\.?0+$/, "");
export const fmtB = (v: number) => (v >= 1e6 ? (v / 1e6).toFixed(v % 1e6 ? 2 : 0) + " MB" : Math.round(v / 1000) + " kB");
export const fmtU = (v: number) =>
  v >= 1e12 ? trim(v / 1e12) + "T" : v >= 1e9 ? trim(v / 1e9) + "G" : trim(v / 1e6) + "M";
const bodyKB = (B: number) => Math.round((B * 40) / 260);
const esc = (s: string) =>
  s.replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c] as string);

const VIEWS: Record<View, [number, number, number]> = {
  iso: [SPAN + 14, YTOP * 2.4, SPAN + 17],
  top: [SPAN / 2, 30, SPAN / 2 + 0.01],
  front: [SPAN / 2, YTOP / 3, 30],
  side: [30, YTOP / 3, SPAN / 2],
};
const TARGET = new THREE.Vector3(SPAN / 2, YTOP / 1.9, SPAN / 2);

// Marching squares on a grid of values; returns segment endpoints in grid index space.
function contour(vals: Float32Array, n: number, level: number): [number, number][] {
  const out: [number, number][] = [];
  const interp = (i1: number, j1: number, i2: number, j2: number): [number, number] => {
    const v1 = vals[j1 * n + i1];
    const v2 = vals[j2 * n + i2];
    const t = (level - v1) / (v2 - v1);
    return [i1 + (i2 - i1) * t, j1 + (j2 - j1) * t];
  };
  for (let j = 0; j < n - 1; j++)
    for (let i = 0; i < n - 1; i++) {
      const v0 = vals[j * n + i];
      const v1 = vals[j * n + i + 1];
      const v2 = vals[(j + 1) * n + i + 1];
      const v3 = vals[(j + 1) * n + i];
      const pts: [number, number][] = [];
      if (v0 < level !== v1 < level) pts.push(interp(i, j, i + 1, j));
      if (v1 < level !== v2 < level) pts.push(interp(i + 1, j, i + 1, j + 1));
      if (v2 < level !== v3 < level) pts.push(interp(i + 1, j + 1, i, j + 1));
      if (v3 < level !== v0 < level) pts.push(interp(i, j + 1, i, j));
      if (pts.length === 2 || pts.length === 4) out.push(...pts);
    }
  return out;
}

interface Label {
  el: HTMLDivElement;
  pos: THREE.Vector3;
  static: boolean;
}

export class GraduationScene {
  private renderer: THREE.WebGLRenderer;
  private scene = new THREE.Scene();
  private camera = new THREE.PerspectiveCamera(36, 1, 0.1, 300);
  private controls: OrbitControls;
  private staticGroup = new THREE.Group();
  private dynGroup = new THREE.Group();
  private labels: Label[] = [];
  private anim: ((t: number) => void) | null = null;
  private raf = 0;
  private pending = 0;
  private input: SceneInput | null = null;
  private hdr = -1;
  private resizeObs: ResizeObserver;
  private v = new THREE.Vector3();

  constructor(
    private stage: HTMLElement,
    private labelsEl: HTMLElement,
    private themeEl: HTMLElement,
    private cls: LabelClasses,
  ) {
    this.renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    stage.prepend(this.renderer.domElement);
    this.controls = new OrbitControls(this.camera, this.renderer.domElement);
    this.controls.enableDamping = true;
    this.controls.dampingFactor = 0.08;
    this.controls.target.copy(TARGET);
    this.camera.position.set(...VIEWS.iso);
    this.scene.add(this.staticGroup, this.dynGroup);
    this.resizeObs = new ResizeObserver(() => this.resize());
    this.resizeObs.observe(stage);
    this.resize();
    this.raf = requestAnimationFrame(this.frame);
  }

  dispose() {
    cancelAnimationFrame(this.raf);
    cancelAnimationFrame(this.pending);
    this.resizeObs.disconnect();
    this.controls.dispose();
    this.clear(this.staticGroup);
    this.clear(this.dynGroup);
    this.labels.forEach((l) => l.el.remove());
    this.renderer.dispose();
    this.renderer.domElement.remove();
  }

  setView(name: View) {
    const to = new THREE.Vector3(...VIEWS[name]);
    const from = this.camera.position.clone();
    const tgt0 = this.controls.target.clone();
    const t0 = performance.now();
    this.anim = (t) => {
      const u = Math.min(1, (t - t0) / 550);
      const e = u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2;
      this.camera.position.lerpVectors(from, to, e);
      this.controls.target.lerpVectors(tgt0, TARGET, e);
      if (u >= 1) this.anim = null;
    };
  }

  update(input: SceneInput) {
    this.input = input;
    cancelAnimationFrame(this.pending);
    this.pending = requestAnimationFrame(() => {
      if (input.hdr !== this.hdr) this.buildStatic();
      this.buildDynamic();
    });
  }

  retheme() {
    this.hdr = -1;
    if (this.input) this.update(this.input);
  }

  private css(n: string) {
    return getComputedStyle(this.themeEl).getPropertyValue(n).trim();
  }
  private col(n: string) {
    return new THREE.Color(this.css(n) || "#888");
  }
  private ymin() {
    return 3 * (this.input?.hdr ?? 1);
  }
  private ymax() {
    return this.ymin() + VSPAN;
  }
  private sy(v: number) {
    return (v - this.ymin()) * YSCALE;
  }

  private resize() {
    const w = this.stage.clientWidth;
    const h = this.stage.clientHeight;
    if (!w || !h) return;
    this.renderer.setSize(w, h, false);
    this.camera.aspect = w / h;
    this.camera.updateProjectionMatrix();
  }

  private frame = (t: number) => {
    if (this.anim) this.anim(t);
    this.controls.update();
    this.renderer.render(this.scene, this.camera);
    const w = this.stage.clientWidth;
    const h = this.stage.clientHeight;
    for (const l of this.labels) {
      this.v.copy(l.pos).project(this.camera);
      if (this.v.z > 1 || this.v.z < -1) {
        l.el.style.display = "none";
        continue;
      }
      l.el.style.display = "";
      l.el.style.left = ((this.v.x + 1) / 2) * w + "px";
      l.el.style.top = ((1 - this.v.y) / 2) * h + "px";
    }
    this.raf = requestAnimationFrame(this.frame);
  };

  private addLabel(html: string, pos: THREE.Vector3, cls: string[], isStatic: boolean) {
    const el = document.createElement("div");
    el.className = [this.cls.lbl, ...cls].join(" ");
    el.innerHTML = html;
    this.labelsEl.appendChild(el);
    const l = { el, pos, static: isStatic };
    this.labels.push(l);
    return l;
  }
  private dropLabels(isStatic: boolean) {
    this.labels.filter((l) => l.static === isStatic).forEach((l) => l.el.remove());
    this.labels = this.labels.filter((l) => l.static !== isStatic);
  }
  private clear(group: THREE.Group) {
    group.traverse((o: any) => {
      if (o.geometry) o.geometry.dispose();
      if (o.material) o.material.dispose();
    });
    group.clear();
  }
  private line(points: THREE.Vector3[], color: THREE.Color, opts: { dashed?: boolean; opacity?: number } = {}) {
    const g = new THREE.BufferGeometry().setFromPoints(points);
    const m = opts.dashed
      ? new THREE.LineDashedMaterial({ color, dashSize: 0.12, gapSize: 0.1, transparent: true, opacity: opts.opacity ?? 1 })
      : new THREE.LineBasicMaterial({ color, transparent: true, opacity: opts.opacity ?? 1 });
    const l = new THREE.Line(g, m);
    if (opts.dashed) l.computeLineDistances();
    return l;
  }
  private segs(arr: number[], color: THREE.Color, opacity = 1) {
    const g = new THREE.BufferGeometry();
    g.setAttribute("position", new THREE.Float32BufferAttribute(arr, 3));
    return new THREE.LineSegments(g, new THREE.LineBasicMaterial({ color, transparent: true, opacity }));
  }

  private buildStatic() {
    const hdr = this.input?.hdr ?? 1;
    this.hdr = hdr;
    this.clear(this.staticGroup);
    this.dropLabels(true);
    const grid = this.col("--pg-grid");
    const ink = this.col("--pg-ink");
    const yt: number[] = [];
    for (let v = 0; v <= VSPAN; v += 2) yt.push(this.ymin() + v);
    const a: number[] = [];
    // Floor and back wall (z = 0).
    XT.forEach((B) => {
      const x = sx(B);
      a.push(x, 0, 0, x, 0, SPAN, x, 0, 0, x, YTOP, 0);
    });
    // Floor and left wall (x = 0).
    ZT.forEach((S) => {
      const z = sz(S);
      a.push(0, 0, z, SPAN, 0, z, 0, 0, z, 0, YTOP, z);
    });
    yt.forEach((v) => {
      const y = this.sy(v);
      a.push(0, y, 0, SPAN, y, 0, 0, y, 0, 0, y, SPAN);
    });
    this.staticGroup.add(this.segs(a, grid, 0.9));
    const e = [0, 0, 0, SPAN, 0, 0, 0, 0, 0, 0, 0, SPAN, 0, 0, 0, 0, YTOP, 0, SPAN, 0, 0, SPAN, 0, SPAN, 0, 0, SPAN, SPAN, 0, SPAN];
    this.staticGroup.add(this.segs(e, ink, 0.8));
    const mk = (t: string, p: THREE.Vector3, c: string) => this.addLabel(t, p, [c], true);
    const { tick, axis } = this.cls;
    XT.forEach((B) => mk(`<b>${B}</b><small>${bodyKB(B)}</small>`, new THREE.Vector3(sx(B), 0, SPAN + 0.7), tick));
    ZT.forEach((S) =>
      mk(`<b>${S}G</b><small>${fmtU(S * 1e9 * 0.0036)} · ${fmtB(S * 20000)}</small>`, new THREE.Vector3(SPAN + 0.95, 0, sz(S)), tick),
    );
    yt.forEach((v) =>
      mk(`<b>${trim(v)} s</b><small>L_vote ${trim(v - 3 * hdr)}</small>`, new THREE.Vector3(-0.7, this.sy(v), 0), tick),
    );
    mk("EB txs (kB, log scale)<small>EB references (kB) = EB txs × 40/260</small>", new THREE.Vector3(SPAN / 2 - 1.2, 0, SPAN + 2.2), axis);
    mk("Plutus steps (G, log scale)<small>Plutus memory · reference scripts</small>", new THREE.Vector3(SPAN + 2.3, 0, SPAN / 2), axis);
    mk("L_diff<small>L_vote = L_diff − 3·L_hdr</small>", new THREE.Vector3(-0.6, YTOP + 0.8, 0), axis);
  }

  private buildDynamic() {
    const input = this.input;
    if (!input) return;
    this.clear(this.dynGroup);
    this.dropLabels(false);
    const accent = this.col("--pg-accent");
    const lo = this.col("--pg-surface-lo");
    const hi = this.col("--pg-surface-hi");
    const ink = this.col("--pg-ink");
    const ok = this.col("--pg-ok");
    const ymin = this.ymin();
    const ymax = this.ymax();
    const N = 56;
    const vals = new Float32Array(N * N);
    const gx = (i: number) => RANGE.x[0] * Math.pow(RANGE.x[1] / RANGE.x[0], i / (N - 1));
    const gz = (j: number) => RANGE.z[0] * Math.pow(RANGE.z[1] / RANGE.z[0], j / (N - 1));
    for (let j = 0; j < N; j++)
      for (let i = 0; i < N; i++) vals[j * N + i] = Math.min(input.needsInfo(gx(i), gz(j)).need, ymax + 1);

    if (input.showSurface) {
      const pos: number[] = [];
      const colors: number[] = [];
      const idx: number[] = [];
      for (let j = 0; j < N; j++)
        for (let i = 0; i < N; i++) {
          const v = Math.min(vals[j * N + i], ymax);
          pos.push(sx(gx(i)), this.sy(v), sz(gz(j)));
          const c = lo.clone().lerp(hi, Math.min(1, (v - ymin) / VSPAN));
          colors.push(c.r, c.g, c.b);
        }
      for (let j = 0; j < N - 1; j++)
        for (let i = 0; i < N - 1; i++) {
          const p = j * N + i;
          idx.push(p, p + 1, p + N, p + 1, p + N + 1, p + N);
        }
      const g = new THREE.BufferGeometry();
      g.setAttribute("position", new THREE.Float32BufferAttribute(pos, 3));
      g.setAttribute("color", new THREE.Float32BufferAttribute(colors, 3));
      g.setIndex(idx);
      const mesh = new THREE.Mesh(
        g,
        new THREE.MeshBasicMaterial({ vertexColors: true, transparent: true, opacity: 0.5, side: THREE.DoubleSide, depthWrite: false }),
      );
      mesh.renderOrder = 1;
      this.dynGroup.add(mesh);
    }

    // Contours on the surface and on the floor.
    [1, 2, 4, 6, 8, 10, 12]
      .map((v) => ymin + v)
      .forEach((level) => {
        const c = contour(vals, N, level);
        if (!c.length) return;
        const surf: number[] = [];
        const floor: number[] = [];
        let best: [number, number] | null = null;
        c.forEach(([i, j]) => {
          const B = gx(i);
          const S = gz(j);
          floor.push(sx(B), 0.002, sz(S));
          if (input.showSurface) surf.push(sx(B), this.sy(level), sz(S));
          if (!best || S < best[1]) best = [B, S];
        });
        this.dynGroup.add(this.segs(floor, accent, 0.75));
        if (surf.length) this.dynGroup.add(this.segs(surf, accent, 0.9));
        if (best) this.addLabel(trim(level) + " s", new THREE.Vector3(sx(best[0]), 0.02, sz(best[1]) + 0.25), [this.cls.cnt], false);
      });

    // Plan points; the path is solid up to the current step and dashed after it.
    const pts: THREE.Vector3[] = [];
    const groups = new Map<string, { names: string[]; pos: THREE.Vector3; p: Step; need: number; bind: Binding; status: Status[] }>();
    input.steps.forEach((p, i) => {
      const status = input.status[i];
      const cvar = p.color ? `--pg-${p.color}` : input.planColor;
      const c = this.col(cvar);
      const x = sx(p.txs);
      const z = sz(p.steps);
      const y = this.sy(p.diff);
      const ni = input.needsInfo(p.txs, p.steps);
      const done = status === "done";
      const sph = new THREE.Mesh(
        new THREE.SphereGeometry(0.17, 24, 16),
        new THREE.MeshBasicMaterial({ color: c, transparent: done, opacity: done ? 0.45 : 1 }),
      );
      sph.position.set(x, y, z);
      sph.renderOrder = 3;
      this.dynGroup.add(sph);
      // A red ring marks a point below the surface.
      if (p.diff < ni.need) {
        const r = new THREE.Mesh(new THREE.TorusGeometry(0.3, 0.025, 8, 40), new THREE.MeshBasicMaterial({ color: accent }));
        r.position.copy(sph.position);
        r.rotation.x = Math.PI / 2;
        this.dynGroup.add(r);
      }
      // A halo marks the step active on the network.
      if (status === "current") {
        const r = new THREE.Mesh(new THREE.TorusGeometry(0.42, 0.05, 10, 48), new THREE.MeshBasicMaterial({ color: ok }));
        r.position.copy(sph.position);
        r.rotation.x = Math.PI / 2;
        this.dynGroup.add(r);
      }
      this.dynGroup.add(this.line([new THREE.Vector3(x, 0, z), new THREE.Vector3(x, y, z)], c, { dashed: true, opacity: 0.8 }));
      const foot = new THREE.Mesh(
        new THREE.CircleGeometry(0.11, 24),
        new THREE.MeshBasicMaterial({ color: c, transparent: true, opacity: 0.5, side: THREE.DoubleSide }),
      );
      foot.rotation.x = -Math.PI / 2;
      foot.position.set(x, 0.003, z);
      this.dynGroup.add(foot);
      pts.push(new THREE.Vector3(x, y, z));
      const key = [p.txs, p.steps, p.diff].join("|");
      const g = groups.get(key);
      if (g) {
        g.names.push(p.id);
        g.status.push(status);
      } else groups.set(key, { names: [p.id], pos: pts[pts.length - 1], p, need: ni.need, bind: ni.bind, status: [status] });
    });
    // One label per position; steps at the same point share it.
    groups.forEach((g) => {
      const names = g.names.map((n, k) => (g.status[k] === "done" ? "✓ " : "") + esc(n)).join(" · ");
      const cur = g.status.includes("current") ? " <em>current</em>" : "";
      const need = g.need === Infinity ? "> " + trim(ymax) : fmt(g.need);
      const cls = [this.cls.set];
      if (g.status.includes("current")) cls.push(this.cls.current);
      else if (g.status.every((s) => s === "done")) cls.push(this.cls.done);
      const l = this.addLabel(`${names}${cur}<small>L_diff ${fmt(g.p.diff)} s, needs ${need} s (${g.bind})</small>`, g.pos, cls, false);
      l.el.style.setProperty("--c", this.css(g.p.color ? `--pg-${g.p.color}` : input.planColor));
    });
    const ci = input.status.indexOf("current");
    for (let i = 0; i + 1 < pts.length; i++) {
      const travelled = i + 1 <= ci;
      const l = this.line([pts[i], pts[i + 1]], ink, travelled ? { opacity: 0.9 } : { dashed: true, opacity: 0.7 });
      l.renderOrder = 2;
      this.dynGroup.add(l);
    }
  }
}
