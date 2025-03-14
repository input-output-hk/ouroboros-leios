db.rust.aggregate(
[
  {
    $match: {
      "scenario.label": "default"
    }
  },
  {
    $group: {
      _id: "$scenario",
      time_s: {
        $max: "$time_s"
      }
    }
  },
  {
    $match: {
      time_s: {
        $gt: 599
      }
    }
  },
  {
    $replaceWith: {
      $mergeObjects: ["$$ROOT", "$_id"]
    }
  },
  {
    $unset: ["_id", "network", "label"]
  },
  {
    $sort: {
      "leios-stage-length-slots": 1,
      "ib-generation-probability": 1,
      "ib-body-avg-size-bytes": 1
    }
  },
  {
    $out: "rust-complete"
  }
]
)

db["rust-complete"].find()
