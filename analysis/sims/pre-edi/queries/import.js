db[simulator].deleteMany({ scenario: scenario })

db[raw].aggregate([
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

db[raw].drop()
