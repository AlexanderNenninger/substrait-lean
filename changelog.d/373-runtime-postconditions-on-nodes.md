### Runtime-checked postconditions on nodes

`on_unproved="runtime"` now works on nodes built from sources (#373). The
postconditions Lean could not prove are checked at every refresh, on the full
result the first time and then on the rows each batch inserts (keys on the
new state), before the sink commits. A violation raises `PostconditionError`
and the refresh writes nothing. Before, building such a node raised
`VerificationError`. The transform's report marks these postconditions as
checked on data (`CheckedCondition.checked`), and the refresh report lists
them as `ensures` lines next to the preconditions. Downstream transforms
assume only proved postconditions, so a node with checked ones is stored with
`.write` before another transform reads it. An incremental view of an eager
result checks them on every batch too.
