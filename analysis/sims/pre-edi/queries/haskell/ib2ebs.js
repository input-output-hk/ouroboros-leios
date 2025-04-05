db.ib2ebs.deleteMany({simulator: "haskell"})
db.haskell.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "event.tag": "generated",
      "event.kind": "EB"
    }
  },
  {
    $project: {
      _id: 0,
      scenario: 1,
      time: "$time_s",
      eb: "$event.id",
      ib: "$event.input_blocks"
    }
  },
  {
    $unwind: "$ib"
  },
  {
    $group: {
      _id: {
        simulator: "haskell",
        scenario: "$scenario",
        ib: "$ib"
      },
      ebs: {
        $push: {
          eb: "$eb",
          time: "$time"
        }
      }
    }
  },
  {
    $merge: "ib2ebs"
  }
]
)
