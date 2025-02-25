[
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
      ibRate:
        "$scenario.ib-generation-probability",
      ibSize: "$scenario.ib-body-avg-size-bytes",
      ib: "$message.id",
      time: 1,
      dir: "$message.type",
      sender: "$message.sender",
      receiver: "$message.recipient"
    }
  },
  {
    $group: {
      _id: {
        ibRate: "$ibRate",
        ibSize: "$ibSize",
        ib: "$ib",
        sender: "$sender",
        receiver: "$receiver"
      },
      sent: {
        $max: {
          $cond: [
            {
              $eq: ["$dir", "InputBlockSent"]
            },
            "$time",
            null
          ]
        }
      },
      received: {
        $max: {
          $cond: [
            {
              $eq: ["$dir", "InputBlockReceived"]
            },
            "$time",
            null
          ]
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
      simulator: "rust",
      ibRate: "$_id.ibRate",
      ibSize: "$_id.ibSize",
      ib: "$_id.ib",
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
    $merge: {
      into: "flight"
    }
  }
]
