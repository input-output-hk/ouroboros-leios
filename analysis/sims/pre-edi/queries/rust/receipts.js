db.receipts.deleteMany({simulator: "rust"})

db["rust-scenario"].find().forEach(function(s) {
print("-----")
printjson(s["_id"])
if (db.receipts.findOne(Object.assign({simulator: "rust"}, s["_id"]))) {
  print("SKIP")
  return
} else {
  print("COMPUTE")
}
db.rust.aggregate(
[
  {
    $match: {
      "scenario": s["_id"],
      "message.type": {
        $in: [
          "IBGenerated",
          "IBSent",
          "IBReceived",
          "EBGenerated",
          "EBSent",
          "EBReceived",
          "VTBundleGenerated",
          "VTBundleSent",
          "VTBundleReceived",
          "RBGenerated",
          "RBSent",
          "RBReceived"
        ]
      }
    }
  },
  {
    $project: {
      _id: 0,
      scenario: 1,
      kind: {
        $substrBytes: ["$message.type", 0, 2]
      },
      time: "$time_s",
      item: "$message.id",
      producer: "$message.producer",
      sent: {
        $regexMatch: {
          input: "$message.type",
          regex: "Sent$"
        }
      },
      size: {
        $switch: {
          branches: [
            {
              case: {
                $eq: ["$message.type", "IBGenerated"]
              },
              then: "$message.total_bytes"
            },
            {
              case: {
                $eq: ["$message.type", "EBGenerated"]
              },
              then: "$message.bytes"
            },
            {
              case: {
                $eq: [
                  "$message.type",
                  "VTBundleGenerated"
                ]
              },
              then: "$message.bytes"
            },
            {
              case: {
                $eq: ["$message.type", "RBGenerated"]
              },
              then: {
                $add: [
                  "$message.header_bytes",
                  {$sum: "$message.endorsement.bytes"}
                ]
              }
            }
          ],
          default: null
        }
      },
      node_name: {
        $switch: {
          branches: [
            {
              case: {
                $regexMatch: {
                  input: "$message.type",
                  regex: "Generated$"
                }
              },
              then: "$message.producer"
            },
            {
              case: {
                $regexMatch: {
                  input: "$message.type",
                  regex: "Sent$"
                }
              },
              then: "$message.sender"
            },
            {
              case: {
                $regexMatch: {
                  input: "$message.type",
                  regex: "Received$"
                }
              },
              then: "$message.recipient"
            }
          ]
        }
      }
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
      simulator: "rust",
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
