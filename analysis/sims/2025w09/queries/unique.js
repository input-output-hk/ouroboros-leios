[
  {
    $match:
      /**
       * query: The query in MQL.
       */
      {
        "scenario.ib-generation-probability": 15,
        "scenario.ib-body-avg-size-bytes": 100000
      }
  },
  {
    $group:
      /**
       * _id: The id of the group.
       * fieldN: The first field name.
       */
      {
        _id: "$message.type",
        count: {
          $count: {}
        }
      }
  },
  {
    $sort:
      /**
       * Provide any number of field/order pairs.
       */
      {
        _id: 1
      }
  }
]
