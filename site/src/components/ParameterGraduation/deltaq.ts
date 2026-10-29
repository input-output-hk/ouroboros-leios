// DeltaQ core: the two-phase closure-completion model with a fixed-size top-stake committee.
// Ported from analysis.py and two_phase.py of PR 1146 (conditional certification diffusion).

export type Net = "mathis" | "cubic";

export interface Model {
  net: Net;
  seats: number;
  pc: number;
  pf: number;
  beta: number;
  tau: number;
  c: number;
  fexec: number;
  h: number;
  // EB references ceiling in kB.
  refsCap: number;
  // Fraction of EB txs a node misses and fetches (π₁).
  miss: number;
  // Average transaction size in bytes.
  txBytes: number;
  // Per-transaction CPU in ms: full applyTx for missed txs, reapplyTx for the rest and for recovery.
  applyMs: number;
  applySd: number;
  reapplyMs: number;
  reapplySd: number;
}

export const DEFAULT_MODEL: Model = {
  net: "mathis",
  seats: 900,
  pc: 0.99,
  pf: 0.999,
  beta: 0,
  tau: 0.75,
  c: 1.0,
  fexec: 1.0,
  h: 1000,
  refsCap: 600,
  miss: 1 / 6,
  txBytes: 1000,
  applyMs: 0.507,
  applySd: 0.527,
  reapplyMs: 0.07,
  reapplySd: 0.265,
};

// Span of the L_diff axis above its 3·L_hdr floor, in seconds.
export const VSPAN = 14;

// EB references in kB for an EB txs closure of txs kB.
export const refsKB = (m: Model, txs: number) => Math.min((txs * 40) / 260, m.refsCap);

export interface Eval {
  pc: number;
  F: number;
  gv: number;
}

// Time grid of analysis.py: index k is time (k + 1)·DT.
const DT = 0.01;
const N = 4000;
const NODES = 2500;

// TCP transfer model: one-way delays of 12 / 69 / 268 ms RTT, 1 Gbit/s, loss 1e-4.
const OWD = [0.006, 0.0345, 0.134];
const SIZES_KB = [1, 64, 256, 512, 1024, 2048, 4096, 6144, 8192, 10240, 12288];
const MSS = 1460;
const LOSS = 1e-4;
const LINK_BPS = 1e9;

function steadyWindow(net: Net) {
  if (net === "mathis") return MSS / Math.sqrt(LOSS);
  return MSS * Math.pow((0.4 * (4 - 0.3)) / (4 * 0.3), 0.25) * Math.pow(LOSS, -0.75);
}

function tcpTransferTime(sizeKb: number, owd: number, net: Net) {
  const size = sizeKb * 1024;
  const rtt = 2 * owd;
  const bps = LINK_BPS / 8;
  const wMax = Math.min(steadyWindow(net), bps * rtt);
  let t = 0;
  let sent = 0;
  let cwnd = 10 * MSS;
  for (;;) {
    const chunk = Math.min(cwnd, size - sent);
    sent += chunk;
    if (sent >= size) return t + chunk / bps + owd;
    t += rtt;
    cwnd = Math.min(cwnd * 2, wMax);
  }
}

const tables: Partial<Record<Net, number[][]>> = {};
function transferTime(net: Net, dist: number, kb: number) {
  const table = (tables[net] ??= OWD.map((owd) => SIZES_KB.map((s) => tcpTransferTime(s, owd, net))))[dist];
  // np.interp: clamped at both ends.
  if (kb <= SIZES_KB[0]) return table[0];
  const last = SIZES_KB.length - 1;
  if (kb >= SIZES_KB[last]) return table[last];
  let i = 0;
  while (SIZES_KB[i + 1] < kb) i++;
  return table[i] + ((kb - SIZES_KB[i]) / (SIZES_KB[i + 1] - SIZES_KB[i])) * (table[i + 1] - table[i]);
}

// Discrete delay laws as point masses on grid indices.
type Atoms = Map<number, number>;

// Index of cdf_wait(t): the first grid time at or after t, or -1 beyond the grid.
function tickOf(t: number) {
  let i = Math.max(0, Math.ceil(t / DT) - 1);
  while (i > 0 && i * DT >= t) i--;
  while (i < N && (i + 1) * DT < t) i++;
  return i < N ? i : -1;
}

function add(a: Atoms, i: number, p: number) {
  if (i >= 0 && i < N && p > 0) a.set(i, (a.get(i) ?? 0) + p);
}

// Convolution of two laws; offset 0 is analysis.cdf_sequential, 1 is two_phase.sequential.
function conv(a: Atoms, b: Atoms, offset: number): Atoms {
  const r: Atoms = new Map();
  a.forEach((p, i) => b.forEach((q, j) => add(r, i + j + offset, p * q)));
  return r;
}

function mix(parts: [number, Atoms][]): Atoms {
  const total = parts.reduce((s, [w]) => s + w, 0);
  const r: Atoms = new Map();
  for (const [w, a] of parts) a.forEach((p, i) => add(r, i, (w / total) * p));
  return r;
}

function hop(net: Net, kb: number): Atoms {
  const r: Atoms = new Map();
  for (let d = 0; d < 3; d++) add(r, tickOf(transferTime(net, d, kb)), 1 / 3);
  return r;
}

function hops(net: Net, n: number, kb: number): Atoms {
  const one = hop(net, kb);
  let r = one;
  for (let k = 1; k < n; k++) r = conv(r, one, 0);
  return r;
}

// Praos path-length distribution.
const HOP_PROBS: [number, number][] = [
  [1, 0.4],
  [2, 3.91],
  [3, 31.06],
  [4, 61.85],
  [5, 2.78],
];
const blended = (net: Net, kb: number) => mix(HOP_PROBS.map(([n, p]) => [p, hops(net, n, kb)]));

// Phase-two recovery paths from the stake-weighted peer graph (5 peers, 25% holder stake).
const RECOVERY_HOPS = [0.7658, 0.2341, 0.0001];

// Voter validation mixes applyTx for missed txs with reapplyTx for cached ones (law of total variance).
function validationLaw(m: Model) {
  const [a, as, r, rs] = [m.applyMs, m.applySd, m.reapplyMs, m.reapplySd].map((x) => x / 1000);
  const mu = m.miss * a + (1 - m.miss) * r;
  const sigma = Math.sqrt(m.miss * (as ** 2 + (a - mu) ** 2) + (1 - m.miss) * (rs ** 2 + (r - mu) ** 2));
  return { mu, sigma };
}
// At most 16,000 references.
const txCount = (closureKb: number, txBytes: number) => Math.max(1, Math.min(Math.trunc((closureKb * 1000) / txBytes), 16000));

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
                    t * (-0.18628806 + t * (0.27886807 + t * (-1.13520398 + t * (1.48851587 + t * (-0.82215223 + t * 0.17087277)))))))),
    );
  return x >= 0 ? r : 2 - r;
}

// CDF table of the fixed-n CLT law of n transactions, delayed by shift seconds.
function cpuTable(n: number, mu: number, sigma: number, shift: number) {
  const mean = n * mu + shift;
  const sd = Math.max(Math.sqrt(n) * sigma, 1e-9);
  const v = new Float64Array(N);
  // Beyond 12 standard deviations the law is 0 or 1 in double precision.
  const lo = Math.max(0, Math.floor((mean - 12 * sd) / DT) - 1);
  const hi = Math.min(N, Math.ceil((mean + 12 * sd) / DT));
  for (let k = lo; k < hi; k++) v[k] = 0.5 * erfc(-((k + 1) * DT - mean) / sd / Math.SQRT2);
  v.fill(1, hi);
  return v;
}

// Deadline-independent parts of one EB: sorted point masses and dense tables.
interface Core {
  bodyI: Int32Array;
  bodyP: Float64Array;
  dataI: Int32Array;
  dataP: Float64Array;
  fetchCdf: Float64Array;
  // Recovery followed by reapplication, from a recovery start at index 0.
  recovered: Float64Array;
  n: number;
  mu: number;
  sigma: number;
  validation: Map<number, Float64Array>;
}

function sorted(a: Atoms): [Int32Array, Float64Array] {
  const keys = Array.from(a.keys()).sort((x, y) => x - y);
  return [Int32Array.from(keys), Float64Array.from(keys, (k) => a.get(k) as number)];
}

const cores = new Map<string, Core>();
function core(m: Model, closureKb: number): Core {
  const bodyKb = refsKB(m, closureKb);
  const net = m.net;
  const key = [net, closureKb, bodyKb, m.miss, m.txBytes, m.applyMs, m.applySd, m.reapplyMs, m.reapplySd].join("|");
  let c = cores.get(key);
  if (c) return c;
  const missing = m.miss * closureKb;
  const wait: Atoms = new Map([[tickOf(0.001), 1]]);
  const body = blended(net, bodyKb);
  const fetch = missing === 0 ? wait : blended(net, missing);
  const recovery =
    missing === 0 ? wait : mix(RECOVERY_HOPS.map((w, h): [number, Atoms] => [w, w > 0 ? hops(net, h + 1, missing) : new Map()]));
  const n = txCount(closureKb, m.txBytes);
  const reapply = cpuTable(n, m.reapplyMs / 1000, m.reapplySd / 1000, 0);
  const recovered = new Float64Array(N);
  recovery.forEach((p, i) => {
    for (let k = i + 1; k < N; k++) recovered[k] += p * reapply[k - i - 1];
  });
  for (let k = 0; k < N; k++) recovered[k] = Math.min(recovered[k], 1);
  const fetchCdf = new Float64Array(N);
  fetch.forEach((p, i) => (fetchCdf[i] += p));
  for (let k = 1; k < N; k++) fetchCdf[k] += fetchCdf[k - 1];
  const [bodyI, bodyP] = sorted(body);
  const [dataI, dataP] = sorted(conv(body, fetch, 1));
  c = { bodyI, bodyP, dataI, dataP, fetchCdf, recovered, n, ...validationLaw(m), validation: new Map() };
  if (cores.size > 400) cores.clear();
  cores.set(key, c);
  return c;
}

function validation(c: Core, shift: number) {
  let v = c.validation.get(shift);
  if (!v) {
    v = cpuTable(c.n, c.mu, c.sigma, shift);
    if (c.validation.size > 64) c.validation.clear();
    c.validation.set(shift, v);
  }
  return v;
}

// Voter readiness at index k: data arrival followed by validation.
function voterAt(c: Core, v: Float64Array, k: number) {
  let s = 0;
  for (let j = 0; j < c.dataI.length && c.dataI[j] <= k - 1; j++) s += c.dataP[j] * v[k - 1 - c.dataI[j]];
  return Math.min(s, 1);
}

// Two-phase node completion at index k for a vote deadline at index tick (two_phase.node_completion).
function completionAt(c: Core, v: Float64Array, tick: number, k: number) {
  if (k < tick) return voterAt(c, v, k);
  // Nodes with all data by the deadline continue validating.
  let s = 0;
  for (let j = 0; j < c.dataI.length && c.dataI[j] < tick; j++) s += c.dataP[j] * v[k - 1 - c.dataI[j]];
  // The others recover what is still missing from max(body, deadline), then reapply.
  for (let j = 0; j < c.bodyI.length; j++) {
    const b = c.bodyI[j];
    const avail = tick - b - 1;
    const retained = avail > 0 ? c.fetchCdf[avail - 1] : 0;
    const start = Math.max(b, tick - 1);
    if (k - 1 - start >= 0) s += c.bodyP[j] * (1 - retained) * c.recovered[k - 1 - start];
  }
  return Math.min(Math.max(s, 0), 1);
}

// Quorum: a[k] = P(a uniform k-seat subset reaches the stake threshold), from seeded permutations.
const QUORUM_SAMPLES = 50_000;
const lnFact = new Float64Array(NODES + 2);
for (let i = 1; i < lnFact.length; i++) lnFact[i] = lnFact[i - 1] + Math.log(i);
const stakes = Array.from({ length: NODES + 1 }, (_, k) => Math.pow((k + 1) / NODES, 10) - Math.pow(k / NODES, 10)).sort((a, b) => b - a);
const totalStake = stakes.reduce((a, b) => a + b, 0);

interface Quorum {
  K: number;
  k: Int32Array;
  lw: Float64Array;
}
const quorums = new Map<string, Quorum>();

function mulberry32(seed: number) {
  return () => {
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function quorum(seats: number, tau: number, beta: number): Quorum {
  const K = Math.max(1, Math.min(Math.round(seats), NODES));
  const key = `${K}|${tau}|${beta}`;
  let q = quorums.get(key);
  if (q) return q;
  const weights = stakes.slice(0, K);
  const committeeStake = weights.reduce((a, b) => a + b, 0);
  const threshold = tau * totalStake - beta * committeeStake;
  let a: Float64Array;
  if (threshold <= 0) a = new Float64Array(K + 1).fill(1);
  else if (threshold > (1 - beta) * committeeStake) a = new Float64Array(K + 1);
  else {
    const w = weights.map((x) => (1 - beta) * x);
    const counts = new Float64Array(K + 1);
    const rand = mulberry32(164);
    const perm = Int32Array.from(w, (_, i) => i);
    for (let s = 0; s < QUORUM_SAMPLES; s++) {
      let acc = 0;
      let crossing = K;
      for (let j = 0; j < K; j++) {
        const r = j + Math.floor(rand() * (K - j));
        const t = perm[j];
        perm[j] = perm[r];
        perm[r] = t;
        acc += w[perm[j]];
        if (acc >= threshold) {
          crossing = j + 1;
          break;
        }
      }
      counts[crossing]++;
    }
    a = new Float64Array(K + 1);
    let cum = 0;
    for (let k = 0; k <= K; k++) a[k] = (cum += counts[k]) / QUORUM_SAMPLES;
  }
  const ks: number[] = [];
  const lw: number[] = [];
  for (let k = 0; k <= K; k++)
    if (a[k] > 0) {
      ks.push(k);
      lw.push(Math.log(a[k]) + lnFact[K] - lnFact[k] - lnFact[K - k]);
    }
  q = { K, k: Int32Array.from(ks), lw: Float64Array.from(lw) };
  quorums.set(key, q);
  return q;
}

// ln Q(p) = ln Σ_k a[k] Binom(K, k, p), evaluated in log space.
function logQuorum(q: Quorum, p: number) {
  if (q.k.length === 0) return -Infinity;
  const lp = Math.log(p);
  const lq = Math.log1p(-p);
  let max = -Infinity;
  const terms = new Float64Array(q.k.length);
  for (let j = 0; j < q.k.length; j++) {
    const k = q.k[j];
    const t = q.lw[j] + (k === 0 ? 0 : k * lp) + (k === q.K ? 0 : (q.K - k) * lq);
    terms[j] = t;
    if (t > max) max = t;
  }
  if (max === -Infinity) return -Infinity;
  let s = 0;
  // Terms below e^-50 of the largest do not change a double.
  for (let j = 0; j < terms.length; j++) if (terms[j] > max - 50) s += Math.exp(terms[j] - max);
  return Math.min(max + Math.log(s), 0);
}

interface Point {
  c: Core;
  v: Float64Array;
  q: Quorum;
  beta: number;
}

function point(m: Model, B: number, S: number): Point {
  const c = core(m, B);
  // Voters additionally spend c · steps · f_exec on Plutus execution.
  const shift = Math.round(m.c * S * m.fexec) / 1000;
  return { c, v: validation(c, shift), q: quorum(m.seats, m.tau, m.beta), beta: m.beta };
}

const tickAt = (t: number) => Math.min(Math.max(Math.round(t / DT), 1), N - 1);

function logPc(pt: Point, Ld: number) {
  return logQuorum(pt.q, voterAt(pt.c, pt.v, tickAt(Ld) - 1));
}

// Vote deadline t_v = 3·L_hdr + L_vote = L_diff; all-node completion at W = 2·L_diff, given C.
function evalAt(pt: Point, Ld: number): Eval {
  const tick = tickAt(Ld);
  const gv = voterAt(pt.c, pt.v, tick - 1);
  const lpc = logQuorum(pt.q, gv);
  const pc = Math.exp(lpc);
  if (!isFinite(lpc)) return { pc, F: 0, gv };
  const k = Math.min(Math.floor((2 * Ld) / DT) - 1, N - 1);
  const done = completionAt(pt.c, pt.v, tick, k);
  if (done <= 0) return { pc, F: 0, gv };
  const ready = Math.min(gv / done, 1);
  const honest = Math.round((1 - pt.beta) * NODES);
  const lf = honest * Math.log(done) + logQuorum(pt.q, ready) - lpc;
  return { pc, F: Math.exp(Math.min(lf, 0)), gv };
}

export function evalPoint(m: Model, B: number, S: number, Ld: number): Eval {
  return evalAt(point(m, B, S), Ld);
}

export type Binding = "infeasible" | "floor" | "certification" | "diffusion";

// Minimum L_diff and the condition that binds it.
export function needsInfo(m: Model, B: number, S: number): { need: number; bind: Binding } {
  const pt = point(m, B, S);
  const floor = (3 * m.h) / 1000 + 0.1;
  const top = (3 * m.h) / 1000 + VSPAN;
  const lnPc = Math.log(m.pc);
  const okC = (Ld: number) => logPc(pt, Ld) >= lnPc;
  const okF = (Ld: number) => evalAt(pt, Ld).F >= m.pf;
  const bisect = (ok: (Ld: number) => boolean, a: number, b: number, iterations: number) => {
    for (let it = 0; it < iterations; it++) {
      const c = (a + b) / 2;
      if (ok(c)) b = c;
      else a = c;
    }
    return b;
  };
  // P(C) only grows with L_diff, so bisect it directly.
  const lc = okC(floor) ? floor : okC(top + 0.25) ? bisect(okC, floor, top + 0.25, 12) : Infinity;
  // F_full|C need not be monotone: coarse scan, then bisection to about 5 ms.
  const firstF = () => {
    if (okF(floor)) return floor;
    for (let Ld = floor + 0.25; Ld <= top + 0.25; Ld += 0.25) if (okF(Ld)) return bisect(okF, Ld - 0.25, Ld, 6);
    return Infinity;
  };
  const lf = lc === Infinity ? Infinity : firstF();
  const need = Math.max(floor, lc, lf);
  const bind: Binding =
    need === Infinity ? "infeasible" : lc <= floor && lf <= floor ? "floor" : lc >= lf ? "certification" : "diffusion";
  return { need, bind };
}
