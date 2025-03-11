db.rbgen.deleteMany({simulator: "haskell"})
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
      simulator: "haskell",
      scenario: 1,
      time: "$time_s",
      size: "$event.size_bytes",
      "eb-count": {
        $size: "$event.endorsed"
      },
      rb: "$event.id"
    }
  },
  {
    $replaceWith: {
      $mergeObjects: ["$$ROOT", "$scenario"]
    }
  },
  {
    $unset: ["_id", "scenario"]
  },
  {
    $merge: "rbgen"
  }
]
)
