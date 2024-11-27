#!/usr/bin/env nix-shell
#!nix-shell -i bash -p nodejs

set -ve

npm install

npx webpack

mkdir -p ../site/static/cost-estimator/
cp index.html view.css controller.js ../site/static/cost-estimator/
