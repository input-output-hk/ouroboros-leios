db.raw.aggregate([
  {
    $set: {
      scenario: { $literal: scenario },
      simulator: { $literal: simulator },
    }
  },
  {
    $unset: "_id",
  },
  {
    $merge: simulator, 
  }
])
