db.receipts.deleteMany({simulator: "rust"})

db["rust-scenario"].find().forEach(s =>
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
              then: "$message.receiver"
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
)
