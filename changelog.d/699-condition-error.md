### Every condition verify cannot read is named at once

`verify` reads every `requires` and `ensures` condition before it proves
anything. If some cannot be read (an unknown column, SQL the lift does not
read, a construct outside the model), it raises one
`sverify.errors.ConditionError` (an `UnsupportedError`) whose `.errors` maps
each such condition's label to its own refusal; the query is not refused
([#699](https://github.com/AlexanderNenninger/substrait-lean/issues/699)).

An Ibis condition that does not type-check, or names a column the table lacks, raised
`TypeError` or `AttributeError` before and now raises `ConditionError`, a
`ValueError`: `except TypeError` around `verify` no longer catches it.
