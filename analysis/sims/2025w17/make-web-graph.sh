#!/usr/bin/env bash

set -e

cd "$1"

LABEL=$(sed -e '1d;s@\(.*\),\(.*\),\(.*\),\(.*\),\(.*\),\(.*\),\(.*\)@\1 | \2 | \3 | \4 IB/s | \5 B/IB | \6 EB/pipeline | \7 s/stage@' case.csv)

zcat sim.log.gz | ../../queries/vertices.sh /dev/stdin vertices.csv.gz

zcat sim.log.gz | ../../queries/edges.sh /dev/stdin edges.csv.gz

cat << EOI > index.html
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>Leios</title>
  <script src="https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"></script>
  <style>
    #network { width: 100%; height: 90vh; border: 1px solid lightgray; }
  </style>
</head>
<body>
  <h2 style="font-family:monospace">$LABEL</h2>
  <div id="network"></div>

  <!-- Embedded CSV data -->
  <script id="nodes" type="text/csv">
EOI

zcat vertices.csv.gz | grep -v VT >> index.html

cat << EOI >> index.html
  </script>

  <script id="edges" type="text/csv">
EOI

zcat edges.csv.gz | grep -v VT >> index.html

cat << EOI >> index.html
  </script>

  <script>
    function csvToRows(text) {
      return text.trim().split('\n').slice(1).map(line => line.split(',').map(x => x.trim()));
    }

    function colorFromPrefix(prefix) {
      const hash = Array.from(prefix).reduce((acc, ch) => acc + ch.charCodeAt(0), 0);
      const hue = hash * 37 % 360;
      return \`hsl(\${hue}, 70%, 70%)\`;
    }

    function drawNetwork() {
      const nodeCSV = document.getElementById('nodes').textContent;
      const edgeCSV = document.getElementById('edges').textContent;

      const nodeRows = csvToRows(nodeCSV);
      const edgeRows = csvToRows(edgeCSV);

      const nodes = nodeRows.map(([id, kind, node, time, size]) => ({
        id,
        label: id,
        color: colorFromPrefix(id.slice(0, 2)),
        level: Math.floor(time)
      }));

      const edges = edgeRows.map(([from, to]) => ({
        from,
        to,
        arrows: 'to',
        color: colorFromPrefix(to.slice(0, 2)),
      }));

      const container = document.getElementById('network');
      const data = {
        nodes: new vis.DataSet(nodes),
        edges: new vis.DataSet(edges)
      };
      const options = {
        layout: {
          hierarchical: {
            direction: 'LR',  // left-to-right
            sortMethod: 'directed'
          },
          improvedLayout: false
        },
        physics: {
          enabled: true
        },
        edges: {
          arrows: {
            to: { enabled: true, scaleFactor: 1 }
          },
          smooth: true
        }
      };
      const network = new vis.Network(container, data, options);
      setTimeout(() => {
        network.setOptions({ physics: false });
      }, 15000);
    }

    drawNetwork();
  </script>
</body>
</html>
EOI

