db.rawIbs.aggregate([
  {
    $project: {
      _id: 0,
      scenario: { $literal: scenario },
      simulator: { $literal: simulator },
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
      scenario: { $literal: scenario },
      simulator: { $literal: simulator },
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
