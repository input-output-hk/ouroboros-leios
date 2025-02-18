#!/usr/bin/env bash

`which time` --verbose \
cabal run exe:ols -- sim short-leios \
                  --leios-config-file data/simulation/config.default.yaml \
                  --topology-file data/simulation/topo-default-100.yaml \
                  --output-file z.json \
                  --output-seconds 120

mongoimport --host thelio \
            --db leios \
            --collection raw \
            --drop \
            z.log

mongo --host thelio leios << EOI

db.raw.aggregate([
  { $group: { _id: "$event.tag" } },
])

db.raw.aggregate([
  { $match: {
    "event.tag": "generated",
    "event.kind": "IB",
  } },
  { $project: {
    _id: "$event.id",
    time_s: 1,
    size_bytes: "$event.size_bytes",
  } },
  { $out: "ibs"},
])

db.raw.aggregate([
  { $match: {
    "event.tag": "received",
    "event.kind": "IB",
  } },
  { $project: {
    ib: "$event.id",
    node: "$event.node",
    time_s: 1,
  } },
  { $lookup: {
    from: "ibs",
    localField: "ib",
    foreignField: "_id",
    as: "origin",
  } },
  { $project: {
    ib: 1,
    node: 1,
    time_s: 1,
    elapsed_s: { $subtract: [ "$time_s", { $arrayElemAt: ["$origin.time_s", 0] }] },
  } },
  { $out: "ibElapsed" },
])

EOI
