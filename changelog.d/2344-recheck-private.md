### `Report.from_substrait` is the one way to read a stored plan back (breaking)

`sverify.substrait_export.recheck` and `sverify.substrait_export.from_substrait` are removed with no alias: `sv.Report.from_substrait(data)` reads an export and proves its contract again, as before ([#2344](https://github.com/AlexanderNenninger/substrait-lean/issues/2344)).
