db.rust.aggregate([
  {
    $match: {
      "message.type": {
        $in: [
          "InputBlockSent",
          "InputBlockReceived"
        ]
      }
    }
  },
  {
    $project: {
      simulator: 1,
      ibRate:
        "$scenario.ib-generation-probability",
      ibSize: "$scenario.ib-body-avg-size-bytes",
      time: 1,
      ib: "$message.id",
      producer: "$message.producer",
      sent: {
        $eq: ["$message.type", "InputBlockSent"]
      },
      recipient: "$message.recipient"
    }
  },
  {
    $group: {
      _id: {
        simulator: "$simulator",
        ibRate: "$ibRate",
        ibSize: "$ibSize",
        ib: "$ib",
        producer: "$producer"
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
              recipient: "$recipient"
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
      producer: "$_id.producer",
      recipient: "$receipts.recipient"
    }
  },
  {
    $merge: {
      into: "receipts"
    }
  }
])
