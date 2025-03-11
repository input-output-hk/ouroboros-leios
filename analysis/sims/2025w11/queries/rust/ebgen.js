db.ebgen.deleteMany({simulator: "rust"})
db.rust.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "message.type": "EBGenerated"
    }
  },
  {
    $group: {
      _id: {
        simulator: "rust",
        scenario: "$scenario",
        eb: "$message.id"
      },
      node: {
        $first: "$message.producer"
      },
      time: {
        $first: "$time_s"
      },
      size: {
        $first: "$message.bytes"
      },
      "ib-count": {
        $first: {
          $size: "$message.input_blocks"
        }
      }
    }
  },
  {
    $lookup: {
      from: "eb2rbs",
      localField: "_id",
      foreignField: "_id",
      as: "ix"
    }
  },
  {
    $set: {
      rbs: {
        $ifNull: [
          {
            $arrayElemAt: ["$ix.rbs", 0]
          },
          []
        ]
      }
    }
  },
  {
    $set: {
      "rb-count": {
        $size: "$rbs.time"
      },
      "rb-first": {
        $min: "$rbs.time"
      },
      "rb-last": {
        $max: "$rbs.time"
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
    $unset: ["_id", "scenario", "ix", "rbs"]
  },
  {
    $merge: "ebgen"
  }
]
)
