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
      node: "$event.node",
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
        node: "$node_name",
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
    $out: "cpus"
  }
]
)
