db.haskell.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "event.tag": "generated",
      "event.kind": "IB"
    }
  },
  {
    $group: {
      _id: {
        simulator: "haskell",
        scenario: "$scenario",
        ib: "$event.id"
      },
      node: {
        $first: "$event.node_name"
      },
      time: {
        $first: "$time_s"
      },
      size: {
        $first: "$event.size_bytes"
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
    $out: "ibgen"
  }
]
)
