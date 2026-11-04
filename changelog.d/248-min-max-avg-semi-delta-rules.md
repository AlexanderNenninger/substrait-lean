### MIN, MAX, exact AVG, semi and anti joins are maintained from changes

A node that ends in `MIN`, `MAX`, or a `DECIMAL` `SUM` or `AVG` per group is
now maintained from its input's changes, like `COUNT` and integer `SUM`. A
batch that only inserts into a group merges its values into the group's
state; the groups it deletes from are recomputed from the new input, and
only those. A node that ends in a semi or anti join on equal keys keeps a
count of matches per key, so a refresh never reads the right side and reads
the left side only for the keys that gain their first match or lose their
last. Lean proves each equal to a full recompute
(`ExtremeAgg.extreme_maintained`, `ExtremeAgg.map_maintained`,
`SemiDelta.semi_maintained`), and the new state survives a failed commit.
`mean()` of integers, a double, is still recomputed by touched groups. This
is the second stage of
[#248](https://github.com/AlexanderNenninger/substrait-lean/issues/248).
