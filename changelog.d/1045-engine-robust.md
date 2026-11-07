### Postconditions on doubles that hold on every engine run

- A postcondition that reads a double `SUM`, `AVG` or statistic, and holds of
  every value within the column's bound and of its sign, now runs on every
  engine, without `sv.approx`. Before, the whole plan was refused with
  "write it as sv.approx(...)", even for `_.total >= 0`
  ([#1045](https://github.com/AlexanderNenninger/substrait-lean/issues/1045)).
  A postcondition that only the reference's exact value meets is still
  refused, naming `sv.approx` as the way out.
