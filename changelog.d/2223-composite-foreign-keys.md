### Composite foreign keys

`sv.references` takes several columns, as `sv.key` does:
`sv.references("street", "zip", to=[addresses.street, addresses.zip])`, or
`to=("addresses", ["street", "zip"])`. A row whose parts are all non-NULL
must match one row of the referenced table on every part (SQL's MATCH
SIMPLE). The data check, `sv.testing.cases`, the Substrait export and the
ODCS export and read handle it, and `odcs.read` now reads composite
relationships ([#2223](https://github.com/AlexanderNenninger/substrait-lean/issues/2223)).

A pair of columns that do not compare is refused at `verify`, for one column too.

Breaking: `References` has the fields `cols`, `table` and `others` (tuples),
in place of `col` and `other`. A report exported before this change reads back
only once exported again.
