db.eb2rbs.deleteMany({simulator: "haskell"})
db.haskell.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "event.tag": "generated",
      "event.kind": "RB"
    }
  },
  {
    $project: {
      _id: 0,
      scenario: 1,
      time: "$time_s",
      rb: "$event.id",
      eb: "$event.endorsed"
    }
  },
  {
    $unwind: "$eb"
  },
  {
    $group: {
      _id: {
        simulator: "haskell",
        scenario: "$scenario",
        eb: "$eb"
      },
      rbs: {
        $push: {
          rb: "$rb",
          time: "$time"
        }
      }
    }
  },
  {
    $merge: "eb2rbs"
  }
]
)
