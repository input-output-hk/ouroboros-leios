db.eb2rbs.deleteMany({"_id.simulator": "rust"})
db.rust.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "message.type": "RBGenerated",
      "message.endorsement": {
        $ne: null
      }
    }
  },
  {
    $project: {
      _id: 0,
      scenario: 1,
      time: "$time_s",
      rb: {
        $concat: [
          {
            $toString: "$message.slot"
          },
          "-",
          "$message.producer"
        ]
      },
      eb: "$message.endorsement.eb.id"
    }
  },
  {
    $group: {
      _id: {
        simulator: "rust",
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
