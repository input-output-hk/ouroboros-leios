db.ib2ebs.deleteMany({simulator: "rust"})
db.rust.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "message.type": "EBGenerated"
    }
  },
  {
    $project: {
      _id: 0,
      scenario: 1,
      time: "$time_s",
      eb: "$message.id",
      ib: "$message.input_blocks"
    }
  },
  {
    $unwind: "$ib"
  },
  {
    $group: {
      _id: {
        simulator: "rust",
        scenario: "$scenario",
        ib: "$ib.id"
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
