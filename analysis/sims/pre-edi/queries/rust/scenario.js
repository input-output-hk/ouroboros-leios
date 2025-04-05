db.rust.aggregate(
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
    $out: "rust-scenario"
  }
]
)
