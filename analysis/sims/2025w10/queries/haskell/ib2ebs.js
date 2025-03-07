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
    $out: "ib2ebs"
  }
]
)
