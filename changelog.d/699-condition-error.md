### A condition verify cannot read names itself

`verify` raises `sverify.errors.ConditionError` (an `UnsupportedError`) for a
`requires` or `ensures` condition it cannot read: an unknown column, SQL the
lift does not read, or a construct outside the model. `.condition` is the
condition as given and `.reason` says why; the query is not refused
([#699](https://github.com/AlexanderNenninger/substrait-lean/issues/699)).
