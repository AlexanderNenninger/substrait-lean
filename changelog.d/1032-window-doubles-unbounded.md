### Fixes

- A window `SUM`, `AVG`, `VARIANCE` or `STDDEV` of doubles was classed
  `exact`: the plan's bound left window functions out, and the engine's
  value can differ from the reference's
  ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)).
  Such a plan still runs. `Report.epsilon` gives the column no bound
  (`"abs": null`, naming #1032), its route is observed on tested evidence,
  and a tolerance stated on the column is refused.
