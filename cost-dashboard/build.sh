#!/usr/bin/env nix-shell
#!nix-shell -i bash -p nodejs

set -ve

npm install

npx webpack

cp index.html view.css controller.js ../site/static/dashboard/
