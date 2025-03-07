db.haskell.aggregate(
[
  {
    $match: {
      "event.tag": {
        $in: ["Sent", "received", "generated"]
      }
    }
  },
  {
    $project: {
      scenario: 1,
      kind: "$event.kind",
      time: "$time_s",
      item: {
        $cond: {
          if: {
            $eq: ["$event.tag", "Sent"]
          },
          then: {
            $arrayElemAt: ["$event.ids", 0]
          },
          else: "$event.id"
        }
      },
      sent: {
        $eq: ["$event.tag", "Sent"]
      },
      node_name: "$event.node_name"
    }
  },
  {
    $group: {
      _id: {
        scenario: "$scenario",
        kind: "$kind",
        item: "$item"
      },
      producer: {
        $max: {
          $cond: [
            {
              $eq: ["$node_name", null]
            },
            "$$REMOVE",
            "$node_name"
          ]
        }
      },
      sent: {
        $min: "$time"
      },
      receipts: {
        $push: {
          $cond: [
            "$sent",
            "$$REMOVE",
            {
              time: "$time",
              recipient: "$node_name"
            }
          ]
        }
      }
    }
  },
  {
    $unwind: {
      path: "$receipts",
      preserveNullAndEmptyArrays: true
    }
  },
  {
    $project: {
      simulator: "haskell",
      sent: "$sent",
      received: "$receipts.time",
      elapsed: {
        $subtract: ["$receipts.time", "$sent"]
      },
      producer: "$producer",
      recipient: "$receipts.recipient"
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
    $unset: ["_id", "scenario"]
  },
  {
    $out: "receipts"
  }
]
)
