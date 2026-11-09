### Breaking: the engines, errors and environment variables of 1.x

From the API review before 1.0 (`api-review/PROPOSAL.md`, items 7, 8, 9 and
14).

Engines (A5, J3):

- `sverify.engine.Engine` is `"duckdb"`, `"polars"` or `"spark"`, the
  engines of the 1.x promise ([stability](docs/stability.md)), and
  `sverify.engines.ENGINES`, the engines a `Connection` runs plans on, is
  `("duckdb", "polars")`.
- The `iceberg` extra installs `pyiceberg[pyarrow,sql-sqlite]`, which a
  local SQLite catalog needs.

Errors and warnings (H1–H4):

- `sverify.errors.Unsupported` is `UnsupportedError`, and `NotIncremental`
  is `NotIncrementalError`. The old names, and `sverify.engines.Unsupported`,
  still work in this release with a `DeprecationWarning`:

  ```python
  from sverify.errors import UnsupportedError  # was: Unsupported

  try:
      sv.verify(query)
  except UnsupportedError as e:
      ...
  ```
- `SverifyWarning`, a `UserWarning`, is the base of every warning sverify
  issues: `filterwarnings("error", category=SverifyWarning)` fails a CI job
  on any of them. `@sv.transform(on_unproved="warn")` warns with an
  `UnprovedWarning`, and `on_inferred="warn"` with an `InferredWarning`
  (formerly `sverify.contracts.InferredPreconditionWarning`, which warns);
  each has the `.report`.
- Every `SverifyError` has a `code`, a snake_case string that names what
  failed and stays the same across 1.x: `not_proved`, `unsupported`,
  `precondition_failed`, `route_refused`, … ([`sverify.errors`](python/src/sverify/errors.py)).
- The API reference documents every error and warning, grouped by the proof,
  the data, running and setup.

Removed (M): the 0.6 aliases `transform(engine=)`, `transform(infer=)`,
`verify(infer=)`, `ContractedTransform.infer`, `Report.run(check_inputs=)`,
`Report.needs_text()`, `Report.needs_lines()`, `Node.plan`,
`route="reference"`, `to_sql(tie_free=)` and `run_spark(tie_free=)`.
`ContractedTransform` takes every argument after the function by keyword
(`@sv.transform` builds it).

Environment variables (J1, J2):

- `SVERIFY_CHECKER` is the path to a `substrait-check` binary, where it was
  `SVERIFY_CHECK`, which still works with a `DeprecationWarning`.
  `SVERIFY_PREBUILT_CHECKER` replaces `SVERIFY_PREBUILT_CHECK`, which is
  read too.
- `SVERIFY_TEMP_DIRECTORY` sets DuckDB's `temp_directory`, where it was
  `SVERIFY_SPILL_DIRECTORY` (0.6), which still works with a
  `DeprecationWarning`.
- The guide lists every variable with its flag and its Python keyword
  ([environment variables](docs/guide.md#environment-variables)).
