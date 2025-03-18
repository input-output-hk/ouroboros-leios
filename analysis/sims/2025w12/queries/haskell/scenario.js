db.rust.aggregate(
[
  {
    $group: {
      _id: "$scenario"
    }
  },
  {
    $out: "haskell-scenario"
  }
]
)
