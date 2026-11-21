### ODCS's published examples read

`sverify.odcs.read` is checked against the 42 example contracts the Open Data
Contract Standard publishes for v3.2.0: 151 conditions read, every unread rule
with its reason and issue, and 95 of the schema objects export and read back
to the same conditions ([#864](https://github.com/AlexanderNenninger/substrait-lean/issues/864)).
`read` now takes a quality rule's SQL that names its object (`SELECT COUNT(*)
FROM orders WHERE …`, in any case), and leaves unread a timestamp bound with a
time zone on a column without one, which DuckDB's cast would have dropped; a
bound on a column with a time zone is cast to `TIMESTAMPTZ`.
A physical type that DuckDB reads as an array (`varchar[3]`) becomes an array
only where the logical type says `array` or says nothing; under `string` it is
a string, as ODCS's AdventureWorks example means it.
