db.raw.aggregate([
  { 
    $match: {
      "event.tag": "generated",
      "event.kind": "IB",
    } 
  },
  { 
    $project: {
      ib: "$event.id",
      time_s: 1,
      size_bytes: "$event.size_bytes",
    } 
  },
  { 
    $out: "rawIbs"
  },
])

db.raw.aggregate([
  { 
    $match: {
      "event.tag": "received",
      "event.kind": "IB",
    } 
  },
  { 
    $project: {
      ib: "$event.id",
      node: "$event.node",
      time_s: 1,
    } 
  },
  { 
    $lookup: {
      from: "rawIbs",
      localField: "ib",
      foreignField: "ib",
      as: "origin",
    } 
  },
  { 
    $project: {
      ib: 1,
      node: 1,
      time_s: 1,
      elapsed_s: { 
        $subtract: [ "$time_s", { $arrayElemAt: ["$origin.time_s", 0] }] 
      },
    } 
  },
  { 
    $out: "rawIbsElapsed" 
  },
])

db.rawIbs.aggregate([
  {
    $project: {
      _id: 0,
      scenario: { $literal: s },
      ib: 1,
      time_s: 1,
      size_bytes: 1,
    }
  },
  {
    $merge: "ibs", 
  }
])

db.rawIbsElapsed.aggregate([
  {
    $project: {
      _id: 0,
      scenario: { $literal: s },
      ib: 1,
      node: 1,
      time_s: 1,
      elapsed_s: 1, 
    }
  },
  {
    $merge: "ibsElapsed", 
  }
])
