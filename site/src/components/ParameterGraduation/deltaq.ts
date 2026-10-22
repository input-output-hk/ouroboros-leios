// DeltaQ core: sampled improved-leios model with a fixed-size top-stake committee.
// Ported from analysis.py on the conditional-certification-diffusion-numerical-report branch.

export type Net = "mathis" | "cubic";
export type Body = "plan" | "report";

export interface Model {
  net: Net;
  body: Body;
  seats: number;
  pc: number;
  pf: number;
  beta: number;
  tau: number;
  c: number;
  fexec: number;
  h: number;
}

export const DEFAULT_MODEL: Model = {
  net: "mathis",
  body: "plan",
  seats: 900,
  pc: 0.99,
  pf: 0.999,
  beta: 0,
  tau: 0.75,
  c: 1.0,
  fexec: 1.0,
  h: 1000,
};

// Span of the L_diff axis above its 3·L_hdr floor, in seconds.
export const VSPAN = 14;

export interface Samples {
  dt: number;
  n: number;
  sizes_kB: number[];
  models: Record<string, Record<string, { G: string[]; G_apply: string[] }>>;
}

interface EvalOpts {
  model: string;
  mode: string;
  tau: number;
  beta: number;
  seats: number;
}

export interface Eval {
  pc: number;
  F: number;
  gv: number;
}

export interface DQ {
  evalAt: (o: EvalOpts, B: number, shift: number, tv: number, tf: number) => Eval;
}

export function makeDQ(S: Samples): DQ {
  // Each sample array holds float32 values of 1 − G; keep ln(1 − G).
  const dec = (b64: string) => {
    const bin = atob(b64);
    const u8 = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) u8[i] = bin.charCodeAt(i);
    const f = new Float32Array(u8.buffer);
    const v = new Float32Array(f.length);
    for (let i = 0; i < f.length; i++) v[i] = Math.log(Math.max(f[i], 1e-30));
    return v;
  };
  const laws: Record<string, Record<string, { G: Float32Array[]; A: Float32Array[] }>> = {};
  for (const m in S.models) {
    laws[m] = {};
    for (const md in S.models[m]) {
      laws[m][md] = { G: S.models[m][md].G.map(dec), A: S.models[m][md].G_apply.map(dec) };
    }
  }
  const sizes = S.sizes_kB;
  const lsz = sizes.map(Math.log);
  const n = S.n;
  const dt = S.dt;
  const NODES = 2500;
  // Synthetic stake distribution from analysis.py: ((k+1)/n)^10 − (k/n)^10, k = 0..n.
  const stakes: number[] = [];
  for (let k = 0; k <= NODES; k++) stakes.push(Math.pow((k + 1) / NODES, 10) - Math.pow(k / NODES, 10));
  stakes.sort((a, b) => b - a);
  const total = stakes.reduce((a, b) => a + b, 0);
  const cmCache = new Map<number, { M: number; M2: number; S_active: number }>();

  // M, M2 and S_active as _committee_moments(2500, seats).
  function committee(seats: number) {
    seats = Math.max(1, Math.min(Math.round(seats), stakes.length));
    let r = cmCache.get(seats);
    if (r) return r;
    let sum = 0;
    for (let i = 0; i < seats; i++) sum += stakes[i];
    let M2 = 0;
    for (let i = 0; i < seats; i++) {
      const w = (stakes[i] * seats) / sum;
      M2 += w * w;
    }
    r = { M: seats, M2, S_active: (total * seats) / sum };
    cmCache.set(seats, r);
    return r;
  }

  // Laws for B kB of EB txs, log-linear between grid sizes.
  const cache = new Map<string, { g: Float32Array; a: Float32Array }>();
  function law(model: string, mode: string, B: number) {
    const key = model + mode + B.toFixed(3);
    let r = cache.get(key);
    if (r) return r;
    const lb = Math.log(Math.min(Math.max(B, sizes[0]), sizes[sizes.length - 1]));
    let i = 0;
    while (i < sizes.length - 2 && lsz[i + 1] < lb) i++;
    const w = (lb - lsz[i]) / (lsz[i + 1] - lsz[i]);
    const L = laws[model][mode];
    const g = new Float32Array(n);
    const a = new Float32Array(n);
    for (let k = 0; k < n; k++) {
      g[k] = L.G[i][k] * (1 - w) + L.G[i + 1][k] * w;
      a[k] = L.A[i][k] * (1 - w) + L.A[i + 1][k] * w;
    }
    r = { g, a };
    if (cache.size > 600) cache.clear();
    cache.set(key, r);
    return r;
  }

  // Linear in ln(1 − G) between samples t_k = (k+1)·dt.
  function lnOneMinus(v: Float32Array, t: number) {
    const x = t / dt - 1;
    if (x < 0) return 0;
    if (x >= n - 1) return v[n - 1];
    const k = Math.floor(x);
    const w = x - k;
    return v[k] * (1 - w) + v[k + 1] * w;
  }
  const at = (v: Float32Array, t: number) => (t <= 0 ? 0 : 1 - Math.exp(lnOneMinus(v, t)));
  const oneMinusAt = (v: Float32Array, t: number) => (t <= 0 ? 1 : Math.exp(lnOneMinus(v, t)));

  // Numerical Recipes erfcc, relative error < 1.2e-7.
  function erfc(x: number) {
    const z = Math.abs(x);
    const t = 1 / (1 + 0.5 * z);
    const r =
      t *
      Math.exp(
        -z * z -
          1.26551223 +
          t *
            (1.00002368 +
              t *
                (0.37409196 +
                  t *
                    (0.09678418 +
                      t *
                        (-0.18628806 +
                          t * (0.27886807 + t * (-1.13520398 + t * (1.48851587 + t * (-0.82215223 + t * 0.17087277)))))))),
      );
    return x >= 0 ? r : 2 - r;
  }

  // Stake-weighted quorum; an active adversary holds beta of the committee weight.
  function Q(p: number, o: EvalOpts) {
    const C = committee(o.seats);
    const mu = (1 - o.beta) * C.M * p + o.beta * C.M;
    const v = (1 - o.beta) * C.M2 * p * (1 - p);
    const th = o.tau * C.S_active;
    if (v < 1e-24) return mu >= th ? 1 : 0;
    return 0.5 * erfc((th - mu) / Math.sqrt(v) / Math.SQRT2);
  }

  // Shift is extra voter CPU (s); tv = 3·L_hdr + L_vote; tf = tv + L_diff.
  function evalAt(o: EvalOpts, B: number, shift: number, tv: number, tf: number): Eval {
    const L = law(o.model, o.mode, B);
    const gv = at(L.g, tv - shift);
    const pc = Q(gv, o);
    if (pc <= 0) return { pc, F: 0, gv };
    const gt = at(L.g, tf - shift);
    const Nh = Math.round((1 - o.beta) * NODES);
    const om = oneMinusAt(L.a, tf);
    const powN = om >= 1 ? 0 : Math.exp(Nh * Math.log1p(-om));
    const pf = gt > 0 ? Math.min(gv / gt, 1) : 1;
    return { pc, F: Math.min(1, (powN * Q(pf, o)) / pc), gv };
  }

  return { evalAt };
}

// Evaluate a point at a given L_diff (s): t_v = 3·L_hdr + L_vote = L_diff, t_f = W = 2·L_diff.
export function evalPoint(dq: DQ, m: Model, B: number, S: number, Ld: number): Eval {
  const shift = (m.c * S * m.fexec) / 1000;
  return dq.evalAt({ model: m.net, mode: m.body, tau: m.tau, beta: m.beta, seats: m.seats }, B, shift, Ld, 2 * Ld);
}

export type Binding = "infeasible" | "floor" | "certification" | "diffusion";

// Minimum L_diff and the condition that binds it.
export function needsInfo(dq: DQ, m: Model, B: number, S: number): { need: number; bind: Binding } {
  const floor = (3 * m.h) / 1000 + 0.1;
  const top = (3 * m.h) / 1000 + VSPAN;
  const okC = (Ld: number) => evalPoint(dq, m, B, S, Ld).pc >= m.pc;
  const okF = (Ld: number) => evalPoint(dq, m, B, S, Ld).F >= m.pf;
  // Coarse scan, then bisection to about 5 ms.
  const first = (ok: (Ld: number) => boolean) => {
    if (ok(floor)) return floor;
    let lo = floor;
    for (let Ld = floor + 0.25; Ld <= top + 0.25; Ld += 0.25) {
      if (ok(Ld)) {
        let a = lo;
        let b = Ld;
        for (let it = 0; it < 6; it++) {
          const c = (a + b) / 2;
          if (ok(c)) b = c;
          else a = c;
        }
        return b;
      }
      lo = Ld;
    }
    return Infinity;
  };
  const lc = first(okC);
  const lf = first(okF);
  const need = Math.max(floor, lc, lf);
  const bind: Binding =
    need === Infinity ? "infeasible" : lc <= floor && lf <= floor ? "floor" : lc >= lf ? "certification" : "diffusion";
  return { need, bind };
}
