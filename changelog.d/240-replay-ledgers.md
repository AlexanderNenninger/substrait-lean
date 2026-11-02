### The DuckDB replay's ledgers come from the SQL lift

`characterization/duckdb/*.json` now record the sqllogictest replay through the SQL lift on `main`, with #338's fixes (#240). Over 121 areas and 46,283 queries: 8,449 agree, 265 disagree, 22,931 refused, 14,638 skipped. The README's summary table is regenerated.

The replay itself:
- logs queries slower than 10 s;
- writes its summary table again: it no longer fails on `probes.json`.

Two lift regressions from #338 are fixed:
- A string read as a decimal rounds half away from zero past the scale, as DuckDB does, instead of being refused.
- A double constant is folded into a decimal where the decimal holds it exactly (`1e1::DECIMAL(38,0)`).
