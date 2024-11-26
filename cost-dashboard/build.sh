#!/usr/bin/env nix-shell
#!nix-shell -i bash -p nodejs

set -ve

npm install

npx webpack

mkdir -p tmp
cp index.html view.css controller.js tmp/
ipfs add --pin=false --recursive=true tmp
