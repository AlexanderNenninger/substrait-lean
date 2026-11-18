### `Report.deterministic` is a theorem

`Report.deterministic` is now `Rel.detPlan`, and when it is true every result
the reference allows is the checker's up to row order
(`check_deterministic_sound`, #1484 finding 9). Before, it checked only ties
in windows, ordered aggregates and `LIMIT`s. It now turns false in four more
places, and `tie_places` names each one:

- `MIN` or `MAX` over doubles, a group key over doubles, or a `DISTINCT` over
  doubles, where the reference keeps any member of a class (`0.0` and
  `-0.0`, the NaNs; D31);
- `QUANTILE_CONT` of doubles (the median), which may be any double between
  the two neighbours;
- an aggregate the checker has not proved a function of its values, such as
  `AVG` of integers;
- an ordered aggregate whose argument is a sort column holding doubles, since
  `0.0` and `-0.0` tie.

A `LIMIT` over an `ORDER BY` on a key stays deterministic, and so does an
ordered aggregate (`first`, `last`, `group_concat`, `mode`, `arg_min`) whose
group and order hold a key. A `LIMIT` over a clustered sort is no longer
deterministic, because the reference leaves the order of the groups open.
Over 2,394 recorded requests, 50 turn false: 22 for `MIN`/`MAX` over doubles,
17 for an `AVG` of integers, 6 for the median of doubles, 4 for a group key
over doubles and 1 for an ordered `ARRAY_AGG` over ties. None turns true. A
rerun requirement (`reproducible=`) refuses these plans.
