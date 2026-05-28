import { useViewerState } from "../state/useViewerState";
import { providerColor } from "../utils/colors";

function rgbToCss([r, g, b]: [number, number, number], alpha = 1) {
  return `rgba(${r}, ${g}, ${b}, ${alpha})`;
}

export default function LegendPanel() {
  const topology = useViewerState((s) => s.topology);
  const excluded = useViewerState((s) => s.excludedProviders);
  const toggleExcluded = useViewerState((s) => s.toggleExcludedProvider);

  if (!topology) return null;

  const providers = topology.provider_summary.slice(0, 12);

  return (
    <div className="absolute top-3 right-3 z-10 w-64 rounded-lg bg-slate-800/90 backdrop-blur border border-slate-700 p-3 shadow-lg">
      <div className="text-xs uppercase tracking-wider text-slate-400 mb-2">
        Providers (click to drop)
      </div>
      <div className="space-y-1 max-h-72 overflow-y-auto">
        {providers.map((p) => {
          const isExcluded = excluded.has(p.provider);
          const stakePct = (
            (p.stake / topology.meta.total_stake_ada) *
            100
          ).toFixed(1);
          return (
            <button
              key={p.provider}
              onClick={() => toggleExcluded(p.provider)}
              className={
                "w-full flex items-center justify-between gap-2 px-2 py-1 rounded text-xs " +
                (isExcluded
                  ? "bg-slate-900/70 text-slate-500 line-through"
                  : "hover:bg-slate-700/60 text-slate-200")
              }
            >
              <span className="flex items-center gap-2 truncate">
                <span
                  className="inline-block h-3 w-3 rounded-sm border border-slate-900"
                  style={{ background: rgbToCss(providerColor(p.provider)) }}
                />
                <span className="truncate">{p.provider}</span>
              </span>
              <span className="font-mono text-slate-400 shrink-0">
                {p.nodes} · {stakePct}%
              </span>
            </button>
          );
        })}
      </div>
      <div className="text-xs text-slate-500 mt-2 pt-2 border-t border-slate-700">
        Arc color = mean latency · Arc width = log(edge count)
      </div>
    </div>
  );
}
