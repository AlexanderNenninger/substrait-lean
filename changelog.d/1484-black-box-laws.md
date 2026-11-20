### Reports name the black-box laws a proof trusts

`Report.black_boxes` maps each black box a plan calls (DuckDB's `entropy`,
`base64`, …) to the laws its row declares, as `sverify.black_box.Law` tuples,
and `str(report)` prints one line for each, such as `trusts: black box entropy
keeps its declared laws (non_null, at_least 0)`. The report's JSON keeps them
under `black_boxes`. If an engine's function ever breaks a declared law, the
checker refuses to print the rows instead of showing the row's sample value
([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)).
