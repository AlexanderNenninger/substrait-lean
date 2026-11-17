### An integer `AVG` is a function of its values

The checker now proves that an `AVG` with an integer result (the truncated
mean) depends on its group's values only, as `SUM` and `COUNT` do
(`AggFn.orderFree`). Two results change:

- `report.deterministic` is true again for a plan whose only open place was
  an integer `AVG` ("not proved a function of its values").
- `run_sharded` runs an integer `AVG` grouped by the split key on each shard
  as it is (`linear`), where it split the mean into a `SUM` and a `COUNT`
  (`two_phase`) before.
