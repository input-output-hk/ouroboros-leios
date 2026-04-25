# Linear Leios (CIP-164) cost estimator

Interactive web tool for estimating operating costs of a Linear Leios node.
Based on the cost analysis in [docs/cost-estimate/](../docs/cost-estimate/).

## Files

- [index.html](index.html) — dashboard UI
- [controller.js](controller.js) — cost model (plain JavaScript, no build step)
- [view.css](view.css) — styling

## Usage

Open `index.html` in a browser, or serve locally:

```
python -m http.server 3000
```

The site at `site/static/cost-estimator/` symlinks back to these files, so
changes here are picked up automatically by the Docusaurus build.
