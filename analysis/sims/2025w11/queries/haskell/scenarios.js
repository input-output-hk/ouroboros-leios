db.haskell.aggregate(
[
  {
    $group: {
      _id: "$scenario",
      count: {
        $count: {}
      }
    }
  },
  {
    $project: {
      _id: 0,
      label: "$_id.label",
      network: "$_id.network",
      ibRate: "$_id.ib-generation-probability",
      ibSize: "$_id.ib-body-avg-size-bytes",
      stageLength: "$_id.leios-stage-length-slots"
    }
  },
  {
    $sort: {
      label: 1,
      network: 1,
      ibRate: 1,
      ibSize: 1,
      stageLength: 1
    }
  }
]
)
