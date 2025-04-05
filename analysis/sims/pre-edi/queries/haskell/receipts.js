db.receipts.deleteMany({simulator: "haskell"})

db["haskell-scenario"].find().forEach(function(s) {
print("-----")
printjson(s["_id"])
if (db.receipts.findOne(Object.assign({simulator: "haskell"}, s["_id"]))) {
  print("SKIP")
  return
} else {
  print("COMPUTE")
}
db.haskell.aggregate(
[
  {
    $match: {
      "scenario": s["_id"],
      "event.tag": {
        $in: ["Sent", "received", "generated"]
      }
    }
  },
  {
    $project: {
      _id: 0,
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
      size: {
        $ifNull :["$event.size_bytes", "$event.msg_size_bytes"]
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
      size: {
        $max: "$size"
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
      size: "$size",
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
    $merge: "receipts"
  }
]
)
})
