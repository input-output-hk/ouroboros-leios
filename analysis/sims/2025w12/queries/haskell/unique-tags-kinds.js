db.haskell.aggregate(
[
  {
    $group: {
      _id: {
        tag: "$event.tag",
        kind: "$event.kind"
      },
      count: {
        $count: {}
      }
    }
  },
  {
    $project: {
      _id: 0,
      tag: "$_id.tag",
      kind: "$_id.kind"
    }
  },
  {
    $sort: {
      tag: 1,
      kind: 1
    }
  }
]
)
