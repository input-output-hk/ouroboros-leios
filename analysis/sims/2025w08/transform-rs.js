db.raw.aggregate([
  { 
    $match: {
      "message.type": "InputBlockGenerated"
    } 
  },
  { 
    $project: {
      ib: "$message.id",
      time_s: "$time",
      size_bytes: null,
    } 
  },
  { 
    $out: "rawIbs"
  },
])

db.raw.aggregate([
  { 
    $match: {
      "message.type": "InputBlockReceived",
    } 
  },
  { 
    $project: {
      ib: "$message.id",
      node: "$message.recipient",
      time_s: "$time",
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
