import { useEffect, useState } from "react";
import { useViewerState } from "../state/useViewerState";
import { loadIndex, loadTopology } from "../data/loader";
import type { AggregateBy, TopologyIndexEntry } from "../data/types";

const AGGREGATE_OPTIONS: { key: AggregateBy; info: string }[] = [
  {
    key: "country",
    info:
      "Group nodes by ISO country code. Each line connects two country centroids " +
      "(arithmetic mean of all node lat/lons in that country). Intra-country edges " +
      "(US→US, DE→DE, …) and nodes without a country tag are dropped. " +
      "Finest granularity — produces the most lines, with the long tail rendered as " +
      "faint hairlines (width and opacity are log-scaled by edge count).",
  },
  {
    key: "provider",
    info:
      "Group nodes by hosting provider AND continent — keys look like AWS/NA, AWS/EU, " +
      "GCP/AS, etc. Splitting by continent avoids the “centroid lands in the ocean” " +
      "artefact for globally-distributed providers. Intra-bucket edges (AWS/NA→AWS/NA) " +
      "are dropped, so you see cross-region and cross-provider flows. Nodes without a " +
      "provider tag (private/on-prem) are dropped.",
  },
  {
    key: "continent",
    info:
      "Group nodes by continent (Europe, North America, Asia, …). At most six " +
      "buckets → ~30 directed pairs — the simplest, most legible view. Best for a " +
      "quick high-level look at transcontinental traffic. Intra-continent edges " +
      "(EU→EU) are dropped — switch to country/provider to recover within-continent " +
      "detail.",
  },
];

export default function ControlPanel() {
  const topologyId = useViewerState((s) => s.topologyId);
  const setTopologyId = useViewerState((s) => s.setTopologyId);
  const setTopology = useViewerState((s) => s.setTopology);
  const setError = useViewerState((s) => s.setError);
  const setLoading = useViewerState((s) => s.setLoading);
  const aggregateBy = useViewerState((s) => s.aggregateBy);
  const setAggregateBy = useViewerState((s) => s.setAggregateBy);
  const showNodes = useViewerState((s) => s.showNodes);
  const setShowNodes = useViewerState((s) => s.setShowNodes);
  const showCorridors = useViewerState((s) => s.showCorridors);
  const setShowCorridors = useViewerState((s) => s.setShowCorridors);
  const showSpread = useViewerState((s) => s.showSpread);
  const setShowSpread = useViewerState((s) => s.setShowSpread);
  const excludedProviders = useViewerState((s) => s.excludedProviders);
  const clearExcludedProviders = useViewerState((s) => s.clearExcludedProviders);
  const topology = useViewerState((s) => s.topology);

  const [index, setIndex] = useState<TopologyIndexEntry[]>([]);

  useEffect(() => {
    loadIndex()
      .then(setIndex)
      .catch((e) => setError(String(e)));
  }, [setError]);

  useEffect(() => {
    setLoading(true);
    loadTopology(topologyId)
      .then(setTopology)
      .catch((e) => setError(String(e)));
  }, [topologyId, setLoading, setTopology, setError]);

  const checkbox = (
    label: string,
    val: boolean,
    set: (b: boolean) => void,
    info?: string,
  ) => (
    <label className="flex items-center gap-2 cursor-pointer text-sm">
      <input
        type="checkbox"
        checked={val}
        onChange={(e) => set(e.target.checked)}
        className="h-3.5 w-3.5 accent-cyan-500"
      />
      <span>{label}</span>
      {info && (
        <span className="group/info relative inline-flex">
          <span
            className="cursor-help w-4 h-4 rounded-full border border-slate-600 text-slate-400 hover:text-slate-200 flex items-center justify-center text-[10px] font-bold leading-none"
            aria-label={info}
          >
            i
          </span>
          <span className="pointer-events-none invisible opacity-0 group-hover/info:visible group-hover/info:opacity-100 transition-opacity absolute z-20 left-6 top-1/2 -translate-y-1/2 w-72 p-2.5 rounded-md bg-slate-900 border border-slate-700 text-xs text-slate-200 leading-snug shadow-xl whitespace-normal">
            {info}
          </span>
        </span>
      )}
    </label>
  );

  return (
    <div className="absolute top-3 left-3 z-10 w-72 rounded-lg bg-slate-800/90 backdrop-blur border border-slate-700 p-3 space-y-3 shadow-lg">
      <div>
        <div className="text-xs uppercase tracking-wider text-slate-400 mb-1">
          Topology
        </div>
        <select
          value={topologyId}
          onChange={(e) => setTopologyId(e.target.value)}
          className="w-full bg-slate-900 border border-slate-700 rounded px-2 py-1.5 text-sm"
        >
          {index.map((t) => (
            <option key={t.id} value={t.id}>
              {t.label} — {t.n_nodes.toLocaleString()} nodes,{" "}
              {t.n_edges.toLocaleString()} edges
            </option>
          ))}
        </select>
      </div>

      <div>
        <div className="text-xs uppercase tracking-wider text-slate-400 mb-1">
          Aggregate corridors by
        </div>
        <div className="flex gap-1 text-sm">
          {AGGREGATE_OPTIONS.map(({ key, info }) => (
            <div key={key} className="group/info relative flex-1">
              <button
                onClick={() => setAggregateBy(key)}
                className={
                  "w-full px-2 py-1 rounded border text-xs " +
                  (aggregateBy === key
                    ? "bg-cyan-600 border-cyan-500 text-white"
                    : "bg-slate-900 border-slate-700 text-slate-300 hover:border-slate-500")
                }
              >
                {key}
              </button>
              <span className="pointer-events-none invisible opacity-0 group-hover/info:visible group-hover/info:opacity-100 transition-opacity absolute z-20 top-full mt-1 left-0 w-72 p-2.5 rounded-md bg-slate-900 border border-slate-700 text-xs text-slate-200 leading-snug shadow-xl whitespace-normal">
                {info}
              </span>
            </div>
          ))}
        </div>
      </div>

      <div>
        <div className="text-xs uppercase tracking-wider text-slate-400 mb-1">
          Layers
        </div>
        <div className="space-y-1">
          {checkbox(
            "Node blobs",
            showNodes,
            setShowNodes,
            "One circle per node, placed at its geographic location. " +
              "Size scales with ADA stake (larger = more stake; relays are uniformly small). " +
              "Color encodes the hosting provider (AWS / GCP / Hetzner / OVH / …). " +
              "Nearby nodes cluster into a single bubble when zoomed out — click a cluster to expand.",
          )}
          {checkbox(
            "Corridor lines",
            showCorridors,
            setShowCorridors,
            "Aggregated peer links between groups (group choice set by the buttons above: country, provider, or continent), drawn as straight lines between group centroids. " +
              "Line width = log of the number of underlying edges in that group-pair. " +
              "Color = mean RTT latency (green ≈ low, red ≈ ≥ 400 ms). " +
              "All corridors render — heavy ones dominate visually, the long tail appears as faint hairlines.",
          )}
          {checkbox(
            "Spread halos",
            showSpread,
            setShowSpread,
            "Per-node translucent circle whose radius equals that node's mean great-circle distance to its peers " +
              "(capped at 5,000 km). Small halo = node peers locally; large halo = globally-distributed peer set. " +
              "Useful for spotting outliers; at world zoom many halos overlap.",
          )}
        </div>
      </div>

      {excludedProviders.size > 0 && (
        <div>
          <div className="text-xs uppercase tracking-wider text-slate-400 mb-1">
            Excluded providers ({excludedProviders.size})
          </div>
          <div className="text-xs text-slate-400 mb-1">
            Click providers in the legend to toggle.
          </div>
          <button
            onClick={clearExcludedProviders}
            className="w-full text-xs px-2 py-1 rounded bg-slate-700 hover:bg-slate-600 text-slate-200"
          >
            Restore all
          </button>
        </div>
      )}

      {topology && (
        <div className="text-xs text-slate-400 pt-2 border-t border-slate-700">
          <div>
            BPs: {topology.meta.n_bps.toLocaleString()} ·{" "}
            Relays: {topology.meta.n_relays.toLocaleString()}
          </div>
          <div>
            Edges: {topology.meta.n_edges.toLocaleString()} ·{" "}
            bidir: {(topology.meta.bidir_rate * 100).toFixed(1)}%
          </div>
          <div>
            Stake: {(topology.meta.total_stake_ada / 1e9).toFixed(2)} B ADA
          </div>
        </div>
      )}
    </div>
  );
}
