#!/usr/bin/env bash
# Fetch Natural Earth 110m countries GeoJSON, strip properties, and clip
# coordinates below 60°S to remove Antarctica (extreme Mercator distortion).
# Source: ~840KB → output: ~200KB.
set -euo pipefail

cd "$(dirname "$0")"

URL="https://raw.githubusercontent.com/nvkelso/natural-earth-vector/master/geojson/ne_110m_admin_0_countries.geojson"
OUTPUT="ne_110m_admin_0_countries.geojson"

echo "Fetching from $URL..."
curl -sL "$URL" -o "$OUTPUT.tmp"

echo "Processing: strip properties, clip below 60°S..."
node -e "
const fs = require('fs');
const data = JSON.parse(fs.readFileSync('$OUTPUT.tmp', 'utf8'));

const MIN_LAT = -60;

function clipRing(ring) {
  return ring.map(([lon, lat]) => [lon, Math.max(lat, MIN_LAT)]);
}

function clipGeometry(geom) {
  if (geom.type === 'Polygon') {
    return { ...geom, coordinates: geom.coordinates.map(clipRing) };
  }
  if (geom.type === 'MultiPolygon') {
    return { ...geom, coordinates: geom.coordinates.map(poly => poly.map(clipRing)) };
  }
  return geom;
}

const slim = {
  type: 'FeatureCollection',
  features: data.features
    .filter(f => {
      // Drop features entirely below the cutoff (Antarctica)
      const coords = JSON.stringify(f.geometry.coordinates);
      const lats = [...coords.matchAll(/,(-?[\\d.]+)\\]/g)].map(m => parseFloat(m[1]));
      return lats.some(lat => lat > MIN_LAT);
    })
    .map(f => ({
      type: 'Feature',
      geometry: clipGeometry(f.geometry),
      properties: {}
    }))
};
fs.writeFileSync('$OUTPUT', JSON.stringify(slim));
"

rm "$OUTPUT.tmp"
echo "Written to $OUTPUT ($(wc -c < "$OUTPUT") bytes)"
