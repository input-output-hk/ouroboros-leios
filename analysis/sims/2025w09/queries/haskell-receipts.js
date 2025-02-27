db.haskell.aggregate([
  {
    $match: {
      "event.kind": "IB",
      "event.tag": {
        $in: ["Sent", "received", "generated"]
      }
    }
  },
  {
    $project: {
      simulator: 1,
      ibRate:
        "$scenario.ib-generation-probability",
      ibSize: "$scenario.ib-body-avg-size-bytes",
      time: "$time_s",
      ib: {
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
        simulator: "$simulator",
        ibRate: "$ibRate",
        ibSize: "$ibSize",
        ib: "$ib"
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
    $unwind: "$receipts"
  },
  {
    $project: {
      _id: 0,
      simulator: "$_id.simulator",
      ibRate: "$_id.ibRate",
      ibSize: "$_id.ibSize",
      ib: "$_id.ib",
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
    $merge: {
      into: "receipts"
    }
  }
])
