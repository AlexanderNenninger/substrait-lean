### `Report.deterministic` holds up to the member of a class of doubles (D48)

`Report.deterministic` is now true when every result the reference allows is
the same up to row order and up to which member of a class of doubles it
keeps: `-0.0` or `0.0`, and which NaN (`check_class_determined_sound`). A
`GROUP BY` or `DISTINCT` key over doubles, `MIN`, `MAX` and `QUANTILE_DISC`
no longer make it false, so a refresh or a sink epoch of `SELECT region,
MAX(price) … GROUP BY region` over a double `price` runs under the default
`reproducible=`. An expression that reads a picked double and can tell `-0.0`
from `0.0`, such as `atan2`, still makes it false, and the report names the
expression.

A rerun requirement that reads the members of a class, `sv.equivalent()`
with exact doubles and exact zeros, still refuses each such pick. The
refusal names the pick and the two ways out: an observation that reads one
zero and one NaN (`floats="plan"`, the sinks' default, or
`zeros="canon"`), or a plan without the pick.

`sv.equivalent(floats="plan")` now compares `-0.0` and `0.0` as equal also
where the plan has no bound on its doubles.
