### Tie order is open in the reference

The reference that plans are verified under leaves the order of ties open
(`tie_order`, `tie_pick`); the deterministic profile fixes it (D24,
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).
`verify` proves postconditions and keys over every order of the ties: a
postcondition over a window, `first()`, `group_concat()` or a `LIMIT` over
ties is proved when it holds for every order, where the report used to say
`undetermined`. `Report.tie_places` names each window, ordered aggregate and
`LIMIT` whose order is not total.
