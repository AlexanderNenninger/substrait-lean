### Values carry their kind

The Lean model's `Value` has a constructor per kind: integers, doubles,
dates, timestamps, times of day, decimals with their scale, strings, lists
and structs ([D29](docs/core-semantics.md#d29-a-value-has-its-kind),
[#923](https://github.com/AlexanderNenninger/substrait-lean/issues/923)).
A double no longer passes for an integer or a timestamp for a date: a
function of one kind gives NULL on another, comparisons take values of one
kind, and contracts track the kind of a column's numbers. `SUM` of decimals
of one scale is a decimal of that scale, whatever the order of the rows.
