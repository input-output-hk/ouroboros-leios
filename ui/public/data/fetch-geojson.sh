#!/usr/bin/env bash
# Fetch Natural Earth 110m countries GeoJSON and strip properties to reduce size.
# Source: ~840KB → output: ~250KB (geometry only, no country metadata).
set -euo pipefail

cd "$(dirname "$0")"

URL="https://raw.githubusercontent.com/nvkelso/natural-earth-vector/master/geojson/ne_110m_admin_0_countries.geojson"
OUTPUT="ne_110m_admin_0_countries.geojson"

echo "Fetching from $URL..."
curl -sL "$URL" -o "$OUTPUT.tmp"

echo "Stripping properties..."
node -e "
const fs = require('fs');
const data = JSON.parse(fs.readFileSync('$OUTPUT.tmp', 'utf8'));
const slim = {
  type: 'FeatureCollection',
  features: data.features.map(f => ({
    type: 'Feature',
    geometry: f.geometry,
    properties: {}
  }))
};
fs.writeFileSync('$OUTPUT', JSON.stringify(slim));
"

rm "$OUTPUT.tmp"
echo "Written to $OUTPUT ($(wc -c < "$OUTPUT") bytes)"
