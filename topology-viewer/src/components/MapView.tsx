import { useEffect, useRef } from "react";
import L from "leaflet";
import "leaflet.markercluster";
import "leaflet/dist/leaflet.css";
import "leaflet.markercluster/dist/MarkerCluster.css";
import "leaflet.markercluster/dist/MarkerCluster.Default.css";

import { useViewerState } from "../state/useViewerState";
import type { NodeFeature, Corridor } from "../data/types";
import { providerColor, latencyColor } from "../utils/colors";

function rgb([r, g, b]: [number, number, number], alpha = 1) {
  return `rgba(${r}, ${g}, ${b}, ${alpha})`;
}

// Marker radius (px) by node kind / stake.
function markerRadius(n: NodeFeature): number {
  if (n.stake <= 0) return 4;                      // relays
  // BPs scale logarithmically with stake.  With x = log10(stake) the formula
  // is flat below 1e3 and then linear in log-stake: 5 at 1k, 14 at 1M,
  // 20 at 100M ADA.
  const x = Math.log10(Math.max(1, n.stake));
  return 5 + 3 * Math.max(0, x - 3);
}

// Escape `<`, `>`, `&`, `"`, `'` so tooltip values that came from external
// data (ticker, provider, …) can't inject markup into the Leaflet tooltip.
function esc(v: unknown): string {
  if (v === null || v === undefined) return "";
  return String(v)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

function buildTooltip(n: NodeFeature): string {
  const stake =
    n.stake > 0 ? `${(n.stake / 1e6).toFixed(2)} M ADA` : "(relay)";
  return `<div style="font-family:ui-monospace,monospace;font-size:11px;line-height:1.4">
    <b>${esc(n.id)}</b> &middot; <span style="opacity:.7">${esc(n.kind)}</span><br/>
    ${n.ticker ? `<b>${esc(n.ticker)}</b><br/>` : ""}
    stake: ${stake}<br/>
    provider: ${esc(n.provider) || "—"}<br/>
    tier: ${esc(n.tier) || "—"}<br/>
    ASN: ${n.asn ?? "—"} &middot; ${esc(n.cc) || "—"}<br/>
    region: ${esc(n.region) || "—"}<br/>
    peers: ${n.peer_count} &middot; spread: ${n.spread_km.toFixed(0)} km
  </div>`;
}

export default function MapView() {
  const mapEl = useRef<HTMLDivElement | null>(null);
  const mapRef = useRef<L.Map | null>(null);
  const clusterRef = useRef<L.MarkerClusterGroup | null>(null);
  const corridorLayerRef = useRef<L.LayerGroup | null>(null);
  const spreadLayerRef = useRef<L.LayerGroup | null>(null);

  const topology = useViewerState((s) => s.topology);
  const aggregateBy = useViewerState((s) => s.aggregateBy);
  const showNodes = useViewerState((s) => s.showNodes);
  const showCorridors = useViewerState((s) => s.showCorridors);
  const showSpread = useViewerState((s) => s.showSpread);
  const excludedProviders = useViewerState((s) => s.excludedProviders);
  const setHoverNode = useViewerState((s) => s.setHoverNode);

  // --- 1. Initialise the map ONCE on mount -----------------------------------
  useEffect(() => {
    if (!mapEl.current || mapRef.current) return;
    const map = L.map(mapEl.current, {
      worldCopyJump: false,
      preferCanvas: true,         // Canvas renderer — orders of magnitude faster
      zoomControl: true,
      attributionControl: true,
    }).setView([35, 10], 3);

    L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png", {
      attribution: "© OpenStreetMap contributors",
      maxZoom: 18,
    }).addTo(map);

    mapRef.current = map;
    return () => {
      map.remove();
      mapRef.current = null;
    };
  }, []);

  // --- 2. (Re-)build the node cluster whenever data or filter changes --------
  useEffect(() => {
    const map = mapRef.current;
    if (!map || !topology) return;

    if (clusterRef.current) {
      map.removeLayer(clusterRef.current);
      clusterRef.current = null;
    }
    if (!showNodes) return;

    const cluster = L.markerClusterGroup({
      maxClusterRadius: 35,
      chunkedLoading: true,
      showCoverageOnHover: false,
      spiderfyOnMaxZoom: true,
      disableClusteringAtZoom: 9,
    });

    const filtered = excludedProviders.size
      ? topology.nodes.filter(
          (n) => !n.provider || !excludedProviders.has(n.provider)
        )
      : topology.nodes;

    for (const n of filtered) {
      const c = providerColor(n.provider);
      const m = L.circleMarker([n.lat, n.lon], {
        radius: markerRadius(n),
        fillColor: rgb(c, 1),
        color: "#222",
        weight: 0.5,
        fillOpacity: n.kind === "bp" ? 0.85 : 0.55,
      });
      m.bindTooltip(buildTooltip(n), {
        sticky: true,
        opacity: 1,
        className: "leaflet-tooltip-dark",
      });
      m.on("mouseover", () => setHoverNode(n));
      m.on("mouseout", () => setHoverNode(null));
      cluster.addLayer(m);
    }

    map.addLayer(cluster);
    clusterRef.current = cluster;
  }, [topology, excludedProviders, showNodes, setHoverNode]);

  // --- 3. (Re-)build corridor lines when toggled / aggregation changes ------
  useEffect(() => {
    const map = mapRef.current;
    if (!map || !topology) return;

    if (corridorLayerRef.current) {
      map.removeLayer(corridorLayerRef.current);
      corridorLayerRef.current = null;
    }
    if (!showCorridors) return;

    const corridors: Corridor[] =
      aggregateBy === "country"
        ? topology.corridors_country
        : aggregateBy === "provider"
        ? topology.corridors_provider
        : topology.corridors_continent;

    // Skip self-corridors + provider-excluded corridors.  No render cap:
    // line width and opacity are already log-scaled by edge count, so weak
    // corridors fade to hairlines automatically, while heavy ones dominate.
    //
    // Provider corridor keys are `<provider>/<continent>` (see
    // `provider_region_key` in build-viewer-data.py), so we split on `/`
    // before checking the excluded-provider set, which stores raw names.
    const providerOf = (key: string) => key.split("/")[0];
    const visible = corridors
      .filter((c) => c.from !== c.to)
      .filter((c) =>
        aggregateBy === "provider"
          ? !excludedProviders.has(providerOf(c.from)) &&
            !excludedProviders.has(providerOf(c.to))
          : true
      );
    if (!visible.length) return;

    const maxCount = Math.max(1, ...visible.map((c) => c.count));
    const logMax = Math.log10(maxCount + 1);

    const group = L.layerGroup();
    for (const c of visible) {
      const w = 0.5 + 5 * (Math.log10(c.count + 1) / logMax);
      const op = 0.2 + 0.6 * (Math.log10(c.count + 1) / logMax);
      const col = rgb(latencyColor(c.mean_latency_ms), 1);
      L.polyline(
        [
          [c.from_lat, c.from_lon],
          [c.to_lat, c.to_lon],
        ],
        { color: col, weight: w, opacity: op, interactive: false }
      ).addTo(group);
    }
    group.addTo(map);
    corridorLayerRef.current = group;
  }, [topology, aggregateBy, showCorridors, excludedProviders]);

  // --- 4. (Re-)build per-node spread halos when toggled ----------------------
  // Each halo is a circle centred on the node with radius = spread_km (capped
  // at 5000 km).  Translucent fill + faint stroke, coloured by provider.  Halos
  // honour the excluded-providers filter so failure scenarios stay consistent.
  useEffect(() => {
    const map = mapRef.current;
    if (!map || !topology) return;

    if (spreadLayerRef.current) {
      map.removeLayer(spreadLayerRef.current);
      spreadLayerRef.current = null;
    }
    if (!showSpread) return;

    const filtered = excludedProviders.size
      ? topology.nodes.filter(
          (n) => !n.provider || !excludedProviders.has(n.provider)
        )
      : topology.nodes;

    const group = L.layerGroup();
    for (const n of filtered) {
      if (!n.spread_km) continue;
      const radius_m = Math.min(n.spread_km, 5000) * 1000;
      const col = rgb(providerColor(n.provider), 1);
      L.circle([n.lat, n.lon], {
        radius: radius_m,
        color: col,
        weight: 1,
        opacity: 0.35,
        fillColor: col,
        fillOpacity: 0.05,
        interactive: false,
      }).addTo(group);
    }
    group.addTo(map);
    spreadLayerRef.current = group;
  }, [topology, showSpread, excludedProviders]);

  return (
    <div className="absolute inset-0">
      <div ref={mapEl} className="h-full w-full" />
    </div>
  );
}
