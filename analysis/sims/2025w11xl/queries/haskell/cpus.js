db.cpus.deleteMany({simulator: "haskell"})
db.haskell.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "event.tag": "Cpu"
    }
  },
  {
    $project: {
      _id: 0,
      scenario: 1,
      slot: {
        $floor: ["$time_s"]
      },
      node: "$event.node_name",
      duration: "$event.duration_s",
      task: {
        $arrayElemAt: [
          {
            $split: ["$event.task_label", ":"]
          },
          0
        ]
      }
    }
  },
  {
    $group: {
      _id: {
        simulator: "haskell",
        scenario: "$scenario",
        node: "$node",
        slot: "$slot",
        task: "$task"
      },
      duration: {
        $sum: "$duration"
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
    $unset: ["_id", "scenario"]
  },
  {
    $merge: "cpus"
  }
]
)
