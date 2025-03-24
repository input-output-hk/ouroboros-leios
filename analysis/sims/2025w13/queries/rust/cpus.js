db.cpus.deleteMany({simulator: "rust"})
db.rust.aggregate(
[
  {
    $match: {
      "scenario.label": "default",
      "message.type": {
        $regex: "^CpuTaskFinished"
      }
    }
  },
  {
    $project: {
      _id: 0,
      scenario: 1,
      slot: {
        $floor: ["$time_s"]
      },
      node: "$message.task.node",
      duration: "$message.cpu_time_s",
      task: "$message.task_type"
    }
  },
  {
    $group: {
      _id: {
        simulator: "rust",
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
