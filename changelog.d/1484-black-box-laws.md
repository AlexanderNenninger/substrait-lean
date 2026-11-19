### Reports name the black-box laws a proof assumes

A report on a plan that calls a black box (DuckDB's `entropy`, `base64`, …)
lists each one with the laws its row declares, as `assumes: black box entropy
keeps its declared laws (non_null, at_least 0)`, and keeps them in its JSON
(`black_boxes`). If an engine's function ever breaks a declared law, the
checker refuses to print the rows instead of showing the row's sample value
([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)).
