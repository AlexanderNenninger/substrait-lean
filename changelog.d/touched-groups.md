### Aggregates recompute only the groups a batch touches

A node that ends in a `GROUP BY` over an input with delta rules no longer
recomputes and diffs its whole result on every refresh. It takes the group
keys of the input rows the batch inserts or deletes, recomputes those groups
(a semi-join on the keys) and replaces their rows, for any measure: MIN, MAX,
AVG, COUNT, SUM and the rest. Lean proves the split
(`TouchedGroups.touched_sound`). `status()` and the refresh summary say which
strategy ran. Other nodes without delta rules are still recomputed and
diffed, and #248 stays the issue for delta rules of aggregates.
