import { useViewerState } from "../state/useViewerState";

export default function HoverTooltip() {
  const n = useViewerState((s) => s.hoverNode);
  if (!n) return null;
  const stakeAda =
    n.stake > 0 ? `${(n.stake / 1e6).toFixed(2)} M ADA` : "0 (relay)";
  return (
    <div className="absolute bottom-3 left-3 z-10 w-80 rounded-lg bg-slate-800/95 backdrop-blur border border-slate-700 p-3 shadow-lg text-xs font-mono">
      <div className="flex items-center justify-between mb-1">
        <span className="text-cyan-400 font-bold">{n.id}</span>
        <span
          className={
            n.kind === "bp"
              ? "px-1.5 py-0.5 bg-cyan-700 rounded text-xs"
              : "px-1.5 py-0.5 bg-slate-700 rounded text-xs"
          }
        >
          {n.kind.toUpperCase()}
        </span>
      </div>
      <div className="grid grid-cols-[80px_1fr] gap-x-2 gap-y-0.5 text-slate-300">
        {n.ticker && (
          <>
            <span className="text-slate-400">ticker</span>
            <span>{n.ticker}</span>
          </>
        )}
        <span className="text-slate-400">stake</span>
        <span>{stakeAda}</span>
        <span className="text-slate-400">provider</span>
        <span>{n.provider || "—"}</span>
        <span className="text-slate-400">tier</span>
        <span>{n.tier || "—"}</span>
        <span className="text-slate-400">ASN</span>
        <span>{n.asn ?? "—"}</span>
        <span className="text-slate-400">country</span>
        <span>{n.cc || "—"}</span>
        <span className="text-slate-400">region</span>
        <span>{n.region || "—"}</span>
        <span className="text-slate-400">peers</span>
        <span>{n.peer_count}</span>
        <span className="text-slate-400">spread</span>
        <span>{n.spread_km.toFixed(0)} km mean</span>
      </div>
      {n.pool_id && (
        <div className="mt-1 pt-1 border-t border-slate-700 text-slate-500 truncate">
          {n.pool_id}
        </div>
      )}
    </div>
  );
}
