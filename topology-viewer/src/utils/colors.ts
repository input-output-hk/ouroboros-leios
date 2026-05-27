// Categorical palette indexed by provider name.  Hyperscalers + major
// commodity hosters get distinguishable hues; long tail is greyish.
export const PROVIDER_COLORS: Record<string, [number, number, number]> = {
  AWS:               [255, 153,   0],   // amber
  GCP:               [ 66, 133, 244],   // blue
  Azure:             [  0, 191, 255],   // cyan
  OVH:               [123,  31, 162],   // purple
  Hetzner:           [220,  53,  69],   // red
  Contabo:           [ 76, 175,  80],   // green
  DigitalOcean:      [ 33, 150, 243],   // light blue
  IONOS:             [255, 235,  59],   // yellow
  "Oracle Cloud":    [255,  87,  34],   // orange-red
  "Vultr / Choopa":  [156,  39, 176],   // violet
  "Akamai/Linode":   [  0, 188, 212],   // teal
  "Cherry Servers":  [233,  30,  99],   // pink
  WorldStream:       [121,  85,  72],   // brown
  Leaseweb:          [121,  85,  72],
  Clouvider:         [121,  85,  72],
  "Green.ch":        [ 76, 175,  80],
  MEVspace:          [121,  85,  72],
  "Cogeco (CA cable ISP)":         [ 96, 125, 139],
  HiVelocity:        [ 96, 125, 139],
  Hostinger:         [ 96, 125, 139],
  "Alibaba Cloud":   [255, 152,   0],
  Cloudflare:        [255, 109,   0],
  HostHatch:         [121,  85,  72],
  "Sunrise (CH residential ISP)":  [121,  85,  72],
  Starlink:          [129, 199, 132],
  "Huawei Cloud":    [183,  28,  28],
  "Tencent Cloud":   [173,  20,  87],
  "Servers.com":     [121,  85,  72],
  Unresolved:        [120, 120, 120],   // grey
  "Other / on-prem": [158, 158, 158],   // light grey
};

export const FALLBACK_COLOR: [number, number, number] = [120, 120, 120];

export function providerColor(p?: string | null): [number, number, number] {
  if (!p) return FALLBACK_COLOR;
  return PROVIDER_COLORS[p] || FALLBACK_COLOR;
}

// Latency colormap: 0ms = green, ≥400ms = red.  Saturating at 400ms
// (rather than the 700ms tail-max) is a deliberate visualisation choice:
// inter-continent corridor *means* never exceed ~383ms and country/provider
// means top out around 395ms (p99), so 400ms uses the full gradient on the
// data that actually exists.  The handful of >400ms edges clamp to red.
export function latencyColor(ms: number): [number, number, number] {
  const x = Math.min(1, Math.max(0, ms / 400));
  // green (low) -> yellow (mid) -> red (high)
  if (x < 0.5) {
    const t = x * 2;
    return [Math.round(40 + 215 * t), 200, 40];
  }
  const t = (x - 0.5) * 2;
  return [255, Math.round(200 - 160 * t), 40];
}
