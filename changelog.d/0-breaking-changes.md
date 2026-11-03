### Breaking changes

Upgrading from 0.3.0, check these first. Each has its own entry below.

- `sv.sql(query)` uses the reference semantics by default, as `sv.verify` and
  `@sv.transform` do (#411). Write `sv.sql(query, semantics="duckdb")` where
  you relied on DuckDB's NaN and `±inf`.
- SQL strings are DuckDB's SQL, read by sverify's own lift. DataFusion's SQL
  planner (#211) and Isthmus (#253) are gone as frontends:
  `sverify.engines.isthmus_json`, `sverify.engines.SQL_PRODUCERS`,
  `sv.connect(sql_producer=...)`, `SVERIFY_ISTHMUS` and `sverify.engine.to_sql`
  are removed. In DuckDB's SQL `7 / 2` is 3.5; write `7 // 2` for integer
  division. `sverify.engines.to_sql` writes SQL from a checked plan.
- `@sv.transform(strict=True)` is `@sv.transform(infer=False)`, and
  `ContractedTransform.strict` is `.infer`, with the opposite truth value
  (#409). `strict=` still works and warns.
- `sv.references(col, table, other)` is
  `sv.references(col, to=other_table.other)` (#412). The positional form still
  works and warns.
- `Connection.datafusion` is deprecated and warns (#413). Run DataFusion
  through `engine="datafusion"`.
- Integer overflow at the declared width is an error that makes a report
  unproved, where it was a warning (#202). Inferred bounds (#244) discharge
  most of it; for the rest, the report's hint names the bound to add to
  `requires`. An integer `SUM` that may overflow is listed in
  `Report.assumed` and checked on the data.
- A double divided by zero raises (#204), and no operation creates a NaN
  (#257): `verify` reports both unless the plan rules them out. Bound the
  divisor or the operands in `requires`, or filter.
- Strings have fewer than 2³² characters, and `substring` with an offset or
  length outside that range is an error (#336). `verify` reports it for a
  column offset unless `requires` bounds it, for example
  `_.start >= -2**32` and `_.start < 2**32`.
- Arithmetic on `FLOAT` (fp32) is refused (#208); cast to `DOUBLE` first.
- No wheels for Intel macOS. There pip and uv build sverify from the sdist,
  which needs [elan](https://github.com/leanprover/elan).
- The maintainer tooling (`sverify.coverage`, `sverify.catalogue`,
  `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`, `sverify.examples`)
  is no longer in the wheel.
