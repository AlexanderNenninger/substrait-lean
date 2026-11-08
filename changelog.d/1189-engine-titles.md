### An engine's name in prose

`ProfilePlugin` gains an optional `title`, the engine's name as prose and
the generated tables write it (`DuckDB`). The contract census, the coverage
table and the realizability page take their engines and names from the
installed plugins ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)),
so Spark's rows in `docs/realizability.md` now read "Spark".
