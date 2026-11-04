### Three SQL lift refusals

The SQL lift refuses `x IN map(…)`, which it read as `FALSE`; an `INTERVAL '… ago'`, whose `ago` SQLGlot drops from a single unit (upstream/bugs/SG-8.json); and a cast to `TIMESTAMP(p)` other than `TIMESTAMP(6)`, which DuckDB keeps at seconds, milliseconds or nanoseconds where the lift kept microseconds. Each gave a wrong result in Lean and in the written SQL ([#626](https://github.com/AlexanderNenninger/substrait-lean/issues/626)).
