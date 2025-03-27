db.ibgen.deleteMany({simulator: "rust"})
db.rust.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "message.type": "IBGenerated"
    }
  },
  {
    $group: {
      _id: {
        simulator: "rust",
        scenario: "$scenario",
        ib: "$message.id"
      },
      node: {
        $first: "$message.producer"
      },
      time: {
        $first: "$time_s"
      },
      size: {
        $first: "$message.total_bytes"
      }
    }
  },
  {
    $lookup: {
      from: "ib2ebs",
      localField: "_id",
      foreignField: "_id",
      as: "ix"
    }
  },
  {
    $set: {
      ebs: {
        $ifNull: [
          {
            $arrayElemAt: ["$ix.ebs", 0]
          },
          []
        ]
      }
    }
  },
  {
    $set: {
      "eb-count": {
        $size: "$ebs.time"
      },
      "eb-first": {
        $min: "$ebs.time"
      },
      "eb-last": {
        $max: "$ebs.time"
      }
    }
  },
  {
    $replaceWith: {
      $mergeObjects: [
        "$$ROOT",
        "$_id",
        "$_id.scenario"
      ]
    }
  },
  {
    $unset: ["_id", "scenario", "ix", "ebs"]
  },
  {
    $merge: "ibgen"
  }
]
)
