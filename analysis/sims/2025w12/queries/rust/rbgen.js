db.rbgen.deleteMany({simulator: "rust"})
db.rust.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "message.type": "RBGenerated"
    }
  },
  {
    $project: {
      simulator: "rust",
      scenario: 1,
      time: "$time_s",
      size: {
        $add: [
          "$message.header_bytes",
           {$sum: "$message.endorsement.bytes"}
        ],
      },
      "eb-count": {
        $cond: {
          if: {
            $eq: ["$message.endorsement", null]
          },
          then: 0,
          else: 1
        }
      },
      rb: {
        $concat: [
          {
            $toString: "$message.slot"
          },
          "-",
          "$message.producer"
        ]
      }
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
