import { useViewerState } from "./state/useViewerState";
import MapView from "./components/MapView";
import ControlPanel from "./components/ControlPanel";
import LegendPanel from "./components/LegendPanel";
import HoverTooltip from "./components/HoverTooltip";

export default function App() {
  const loading = useViewerState((s) => s.loading);
  const error = useViewerState((s) => s.error);

  return (
    <div className="relative w-full h-screen overflow-hidden">
      <MapView />
      <ControlPanel />
      <LegendPanel />
      <HoverTooltip />

      <div className="absolute top-3 left-1/2 -translate-x-1/2 z-20 pointer-events-none text-center">
        <h1 className="text-base font-bold tracking-tight text-slate-100">
          Leios Topology Viewer
        </h1>
        <div className="text-xs text-slate-400">
          v4 / v5 / v6 — Koios epoch 630 nodes · RIPE Atlas latencies · CF
          blockperf edges
        </div>
      </div>

      {loading && (
        <div className="absolute top-16 left-1/2 -translate-x-1/2 z-20 bg-slate-800/90 px-3 py-1 rounded text-xs text-slate-300 border border-slate-700">
          loading…
        </div>
      )}
      {error && (
        <div className="absolute top-16 left-1/2 -translate-x-1/2 z-20 bg-red-900/90 px-3 py-1 rounded text-xs text-red-100 border border-red-700">
          {error}
        </div>
      )}
    </div>
  );
}
