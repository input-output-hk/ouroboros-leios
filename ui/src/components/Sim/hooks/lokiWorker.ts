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

// Selected on the line content alone, deliberately not on a `kind` label.
//
// Whether a cardano-node line carries a `kind` stream label is a property of
// the Loki pipeline, not of the event: against demo/extras/x-ray, Loki promotes
// `kind` for top-level kinds and leaves it unset only where the kind is nested
// (TraceSendRecv and friends). A `kind=""` selector therefore drops exactly the
// Leios events this view exists to show — measured against a live dozen-devnet,
// it returned zero LeiosBlockAnnounced, zero TraceForgedBlock and zero
// CompletedBlockFetch while the unconstrained selector returned all of them.
//
// The risk this trades against is double counting, which would corrupt the
// parser's stateful correlation (cert -> forge -> adopt). That only arises if a
// pipeline writes each line twice, once pre- and once post-label. Ours does not:
// per-kind counts are identical with and without the constraint. Revisit if a
// deployment reintroduces the duplicate write.
// The selector is a regex, not an exact match, because the x-ray pipeline
// labels some traces with a sub-service: vote creation arrives as
// service="cardano-node/leios-voting" while everything else is plain
// "cardano-node". An exact match dropped every LeiosVoted line before the line
// filter below ever ran -- votes appeared to be sent and received but never
// created. Matching the prefix also picks up any future cardano-node/* stream.
// RequestNext is excluded on the stream label, not the line: it is the
// mini-protocol's payload-free pull, it matches none of the names below (checked
// against a live dozen-devnet: zero regex hits on that namespace), and at
// committee size 900 it is half of every trace the devnet emits. Dropping it cut
// lines scanned per poll by 64%, 2.31M -> 0.82M over a 5 minute window.
const QUERY =
  '{service=~"cardano-node.*", ns!~"LeiosNotify.Remote.(Send|Receive).RequestNext"} |~ "BlockFetchServer|MsgBlock|CompletedBlockFetch|MsgLeiosBlock|MsgLeiosBlockTxs|LeiosBlockForged|TraceForgedBlock|TraceAdoptedBlock|LeiosBlockAnnounced|LeiosBlockCertified|MsgLeiosVotes|LeiosVoted"';

const POLL_INTERVAL_MS = 1000;
const MAX_ENTRIES = 5000;
const NS_PER_SEC = 1_000_000_000n;
// How far back the first poll reaches (backfill on connect). Kept short on
// purpose: this is a live view, and against a long-running devnet the matched
// line volume makes deep backfills page for minutes before the view reaches
// "now" (a 500-seat committee produces ~750 matching lines/s, i.e. a 30min
// lookback was ~270 pages). History beyond this belongs to Grafana.
const INITIAL_LOOKBACK_NS = 120n * NS_PER_SEC;
// Overlap re-scanned each poll so entries ingested late (Alloy scrapes files
// every 5s) are still picked up; dedup drops the repeats.
const OVERLAP_NS = 15n * NS_PER_SEC;
const MAX_RETRY_DELAY_MS = 30000;

// Dedup the sliding-window overlap: the same entry is re-fetched on consecutive
// polls (with its original tsNs), so drop repeats keyed by (tsNs + message
// identity). The Alloy double-write is handled upstream by the QUERY selector,
// not here.
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

// One page of the window; throws on transport errors so poll() can back off.
async function fetchPage(
  startNs: bigint,
  endNs: bigint,
): Promise<{ stream: unknown; values?: [string, string][] }[]> {
  const params = new URLSearchParams({
    query: QUERY,
    start: startNs.toString(),
    end: endNs.toString(),
    limit: String(MAX_ENTRIES),
    direction: "forward",
  });
  const resp = await fetch(
    `http://${host}/loki/api/v1/query_range?${params.toString()}`,
  );
  if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
  const json: {
    data?: { result?: { stream: unknown; values?: [string, string][] }[] };
  } = await resp.json();
  return json?.data?.result ?? [];
}

// Pages per poll before giving the event loop a breather. A window can only
// need many pages while catching up (initial backfill, or Loki ingesting a
// backlog); steady state is one or two.
const MAX_PAGES_PER_POLL = 10;

async function poll(): Promise<void> {
  if (cancelled) return;
  const end = nowNs();

  // Drain the whole [sinceNs, end] window with a LOCAL page cursor. The
  // global sinceNs must not advance past entries that Alloy has not shipped
  // yet: it batches file scrapes (~5s), so lines regularly arrive in Loki
  // seconds after their timestamps. Advancing the global cursor to the newest
  // *seen* timestamp mid-drain (as this used to) skipped those stragglers
  // whenever a window hit the entry cap -- with a full committee that is every
  // poll, and the stragglers are whole nodes' vote lines. The overlap re-scan
  // below exists exactly for them; dedup eats the cost.
  const result: { stream: unknown; values?: [string, string][] }[] = [];
  let pageStart = sinceNs;
  let sawFullWindow = true;
  try {
    for (let page = 0; page < MAX_PAGES_PER_POLL; page++) {
      const pageResult = await fetchPage(pageStart, end);
      let pageCount = 0;
      let pageMaxTs = 0n;
      for (const stream of pageResult) {
        for (const [tsNs] of stream.values ?? []) {
          pageCount++;
          const ts = BigInt(tsNs);
          if (ts > pageMaxTs) pageMaxTs = ts;
        }
      }
      result.push(...pageResult);
      if (pageCount < MAX_ENTRIES || pageMaxTs === 0n) break;
      if (page === MAX_PAGES_PER_POLL - 1) {
        // Still capped: leave the tail for the next poll rather than starving
        // the parser; the window is re-fetched from sinceNs, dedup skips what
        // this poll already emitted.
        sawFullWindow = false;
        console.warn(
          `[lokiWorker] window still capped after ${MAX_PAGES_PER_POLL} pages; deferring tail`,
        );
        break;
      }
      // Inclusive re-fetch of the boundary timestamp; dedup covers it.
      pageStart = pageMaxTs;
    }
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

  const json = { data: { result } };
  const events: IServerMessage[] = [];

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

  if (!sawFullWindow) {
    // Deferred tail: keep the cursor, come straight back for the rest.
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
