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
    $out: "eb2rbs"
  }
]
)
