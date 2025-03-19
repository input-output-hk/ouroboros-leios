db.haskell.aggregate(
[
  {
    $group: {
      _id: "$scenario",
      time: {
        $max: "$time_s"
      }
    }
  },
  {
    $out: "haskell-scenario"
  }
]
)
