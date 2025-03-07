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
    $group: {
      _id: {
        simulator: "haskell",
        scenario: "$scenario",
        eb: "$event.id"
      },
      node: {
        $first: "$event.node_name"
      },
      time: {
        $first: "$time_s"
      },
      size: {
        $first: "$event.size_bytes"
      },
      "ib-count": {
        $first: {
          $size: "$event.input_blocks"
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
    $out: "ebgen"
  }
]
)
