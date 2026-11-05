### ODCS contracts

`sverify.odcs` writes a node's contract as an Open Data Contract Standard
document (ODCS v3.2.0) and reads ODCS contracts as conditions
([#791](https://github.com/AlexanderNenninger/substrait-lean/issues/791)).
The export maps NOT NULL columns to `required`, keys to `primaryKey` and
`unique`, value sets, ranges and row caps to quality rules, and the
docstring to descriptions; each rule carries a `sverify` custom property
saying whether it is proved, checked on the data or declared. `odcs.read`
gives the conditions for `requires` or `ensures` and lists, with a warning,
every rule it cannot read. `sverify contract export <file>:<node> --format
odcs` writes it from the command line. YAML needs the new extra
`sverify[odcs]`.
