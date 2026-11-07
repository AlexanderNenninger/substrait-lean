### Postconditions on every allowed result

`contract_sound_allowed` proves a postcondition on every result the
reference allows, every order and grouping of a double `SUM` or `AVG` among
them, where the plan reads no open sum to choose its rows (#899). The report
marks such a postcondition `CheckedCondition.allowed`: one on a plan without
open sums, or one that reads no open sum of an aggregate. Comparisons of the
open sums themselves follow with the tolerance's bound (#929).
