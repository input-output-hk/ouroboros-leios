db.rust.aggregate(
[
  {
    $group: {
      _id: "$scenario"
    }
  },
  {
    $out: "rust-scenario"
  }
]
)
