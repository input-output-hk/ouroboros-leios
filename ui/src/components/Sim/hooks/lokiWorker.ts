// Web Worker that polls Loki's query_range HTTP API off the main thread.
//
// We poll query_range rather than the /tail WebSocket: /tail is best-effort
// and silently omits entries (not counted in `dropped_entries`), whereas
// query_range returns the complete window. A sliding window with overlap
// tolerates Loki's ingestion latency, and the dedup below removes both the
// re-scanned overlap and Loki's duplicate-ingested copies (the Alloy pipeline
// stores each cardano line more than once).
//
// Loki serves no CORS headers, so the demo fronts it with a small CORS-adding
// reverse proxy (see demo/extras/x-ray); the scenario's `loki` host points at
// that proxy and the fetch below hits it directly.

import { IServerMessage } from "@/components/Sim/types";
import { parseStreamValue, resetPendingState } from "./lokiParsers";

export type LokiWorkerRequest =
  | { type: "CONNECT"; lokiHost: string }
  | { type: "DISCONNECT" };

export type LokiConnectionState =
  | "Connecting"
  | "Connected"
  | "NotConnected";

export type LokiWorkerResponse =
  | { type: "CONNECTION_STATE"; state: LokiConnectionState }
  | { type: "EVENTS"; events: IServerMessage[] }
  | { type: "DROPPED"; count: number };

const QUERY =
  '{service="cardano-node"} |~ "BlockFetchServer|MsgBlock|CompletedBlockFetch|MsgLeiosBlock|MsgLeiosBlockTxs|LeiosBlockForged|TraceForgedBlock|TraceAdoptedBlock|LeiosBlockAnnounced|LeiosBlockCertified|MsgLeiosVotes|LeiosVoted"';

const POLL_INTERVAL_MS = 1000;
const MAX_ENTRIES = 5000;
const NS_PER_SEC = 1_000_000_000n;
// How far back the first poll reaches (backfill on connect).
const INITIAL_LOOKBACK_NS = 1800n * NS_PER_SEC;
// Overlap re-scanned each poll so entries ingested late (Alloy scrapes files
// every 5s) are still picked up; dedup drops the repeats.
const OVERLAP_NS = 15n * NS_PER_SEC;
const MAX_RETRY_DELAY_MS = 30000;

// Dedup: a stable per-entry key (raw tsNs + message identity). Loki redelivers
// (double-writes) entries with their original timestamp, and the sliding
// window re-scans an overlap, so the same entry is seen more than once.
const seenEntryKeys = new Set<string>();
const SEEN_ENTRY_CAP = 200_000;

let cancelled = false;
let connected = false;
let host = "";
let sinceNs = 0n;
let retryCount = 0;
let pollTimer: ReturnType<typeof setTimeout> | null = null;

const post = (msg: LokiWorkerResponse) => postMessage(msg);
const nowNs = (): bigint => BigInt(Date.now()) * 1_000_000n;
const setState = (state: LokiConnectionState) =>
  post({ type: "CONNECTION_STATE", state });

const clearTimer = () => {
  if (pollTimer !== null) {
    clearTimeout(pollTimer);
    pollTimer = null;
  }
};

const schedule = (delayMs: number) => {
  clearTimer();
  if (!cancelled) pollTimer = setTimeout(() => void poll(), delayMs);
};

async function poll(): Promise<void> {
  if (cancelled) return;
  const end = nowNs();
  const params = new URLSearchParams({
    query: QUERY,
    start: sinceNs.toString(),
    end: end.toString(),
    limit: String(MAX_ENTRIES),
    direction: "forward",
  });

  let json: {
    data?: { result?: { stream: unknown; values?: [string, string][] }[] };
  };
  try {
    const resp = await fetch(
      `http://${host}/loki/api/v1/query_range?${params.toString()}`,
    );
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    json = await resp.json();
  } catch (error) {
    console.error("[lokiWorker] query_range failed:", error);
    connected = false;
    retryCount++;
    setState("Connecting");
    schedule(Math.min(1000 * 2 ** (retryCount - 1), MAX_RETRY_DELAY_MS));
    return;
  }
  retryCount = 0;
  if (!connected) {
    connected = true;
    setState("Connected");
  }

  const events: IServerMessage[] = [];
  let count = 0;
  let maxTs = 0n;

  // query_range groups the response by stream (one per distinct label set), so
  // entries are ordered within a stream but not globally. The parser correlates
  // events that live in different streams via module-level pending maps
  // (ForgedBlock -> AdoptedBlock for the RB's parent/endorsement, cert -> forge,
  // announcement -> forge), and that only works if it sees them in timestamp
  // order. Flatten every stream and sort by tsNs before parsing.
  const entries: Array<{
    tsNs: string;
    labels: Record<string, string>;
    logLine: string;
  }> = [];
  for (const stream of json?.data?.result ?? []) {
    for (const [tsNs, logLine] of stream.values ?? []) {
      entries.push({
        tsNs,
        labels: stream.stream as Record<string, string>,
        logLine,
      });
    }
  }
  entries.sort((a, b) => {
    const x = BigInt(a.tsNs);
    const y = BigInt(b.tsNs);
    return x < y ? -1 : x > y ? 1 : 0;
  });

  for (const { tsNs, labels, logLine } of entries) {
    count++;
    const tsBig = BigInt(tsNs);
    if (tsBig > maxTs) maxTs = tsBig;
    const parsed = parseStreamValue(
      labels,
      Number(tsNs) / 1_000_000_000,
      logLine,
    );
    if (!parsed) continue;
    const m = parsed.message as {
      type: string;
      id?: string;
      sender?: string;
      recipient?: string;
    };
    const key = `${tsNs}|${m.type}|${m.id ?? ""}|${m.sender ?? ""}|${m.recipient ?? ""}`;
    if (seenEntryKeys.has(key)) continue;
    if (seenEntryKeys.size >= SEEN_ENTRY_CAP) {
      seenEntryKeys.delete(seenEntryKeys.values().next().value as string);
    }
    seenEntryKeys.add(key);
    events.push(parsed);
  }

  if (events.length > 0) {
    post({ type: "EVENTS", events });
  }

  if (count >= MAX_ENTRIES && maxTs > 0n) {
    // Window hit the entry cap; direction=forward gave us the oldest
    // MAX_ENTRIES. Advance to the newest we saw (inclusive re-fetch; dedup
    // covers it) and poll again promptly to drain the rest without a gap.
    console.warn(`[lokiWorker] query_range hit ${MAX_ENTRIES} entries; paginating`);
    sinceNs = maxTs;
    schedule(0);
  } else {
    const next = end - OVERLAP_NS;
    sinceNs = next > sinceNs ? next : sinceNs;
    schedule(POLL_INTERVAL_MS);
  }
}

self.onmessage = (e: MessageEvent<LokiWorkerRequest>) => {
  const req = e.data;
  if (req.type === "CONNECT") {
    cancelled = false;
    connected = false;
    host = req.lokiHost;
    retryCount = 0;
    resetPendingState();
    seenEntryKeys.clear();
    sinceNs = nowNs() - INITIAL_LOOKBACK_NS;
    clearTimer();
    setState("Connecting");
    void poll();
  } else if (req.type === "DISCONNECT") {
    cancelled = true;
    clearTimer();
    setState("NotConnected");
  }
};
