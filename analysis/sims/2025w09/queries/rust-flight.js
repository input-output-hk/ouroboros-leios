db.rust.aggregate([
  {
    $match: {
      simulator: "rust",
      "message.type": {
        $in: [
          "InputBlockSent",
          "InputBlockReceived",
          "EndorserBlockSent",
          "EndorserBlockReceived",
          "PraosBlockSent",
          "PraosBlockReceived",
          "TransactionSent",
          "TransactionReceived"
        ]
      }
    }
  },
  {
    $project: {
      ibRate:
        "$scenario.ib-generation-probability",
      ibSize: "$scenario.ib-body-avg-size-bytes",
      item: "$message.id",
      time: 1,
      kind: {
        $switch: {
          branches: [
            {
              case: {
                $in: [
                  "$message.type",
                  [
                    "InputBlockSent",
                    "InputBlockReceived"
                  ]
                ]
              },
              then: "IB"
            },
            {
              case: {
                $in: [
                  "$message.type",
                  [
                    "EndorserBlockSent",
                    "EndorserBlockReceived"
                  ]
                ]
              },
              then: "EB"
            },
            {
              case: {
                $in: [
                  "$message.type",
                  [
                    "PraosBlockSent",
                    "PraosBlockReceived"
                  ]
                ]
              },
              then: "RB"
            },
            {
              case: {
                $in: [
                  "$message.type",
                  [
                    "TransactionSent",
                    "TransactionReceived"
                  ]
                ]
              },
              then: "Tx"
            }
          ],
          default: "unknown"
        }
      },
      sent: {
        $in: [
          "$message.type",
          [
            "InputBlockSent",
            "EndorserBlockSent",
            "PraosBlockSent",
            "TransactionSent"
          ]
        ]
      },
      sender: "$message.sender",
      receiver: "$message.recipient"
    }
  },
  {
    $group: {
      _id: {
        ibRate: "$ibRate",
        ibSize: "$ibSize",
        item: "$item",
        kind: "$kind",
        sender: "$sender",
        receiver: "$receiver"
      },
      sent: {
        $max: {
          $cond: ["$sent", "$time", null]
        }
      },
      received: {
        $max: {
          $cond: ["$sent", null, "$time"]
        }
      }
    }
  },
  {
    $match: {
      $expr: {
        $ne: ["$received", null]
      }
    }
  },
  {
    $project: {
      _id: 0,
      simulator: "rust",
      ibRate: "$_id.ibRate",
      ibSize: "$_id.ibSize",
      kind: "$_id.kind",
      item: "$_id.item",
      sender: "$_id.sender",
      receiver: "$_id.receiver",
      sent: 1,
      received: 1,
      delay: {
        $subtract: ["$received", "$sent"]
      }
    }
  },
  {
    $out: "flight"
  }
])
