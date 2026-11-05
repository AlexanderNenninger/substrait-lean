### Public API additions

- `sverify.__version__` is the installed version, and `dir(sverify)` lists
  `__all__` and `__version__`; the submodules import as before.
- `node.to_substrait()` and `transform.to_substrait()` export the report of
  a node and of a transform's last call, as `report.to_substrait()` does;
  `node.report` is that report.
- `PreconditionError` carries the table (`.source`), the condition
  (`.condition`) and up to ten of the rows that break it as an Arrow table
  (`.rows`).
- `sv.key("id")` states a primary key: `sv.unique("id")` and
  `'"id" IS NOT NULL'`.
- `report.not_null` lists the output columns the checker shows are never NULL, and
  a stored node writes them as NOT NULL columns and records them in its
  contract, with those `ensures` states.
- Each `Needed` of `report.needs` has its `condition`, ready for
  `requires=`: an Ibis deferred for an Ibis transform, a SQL string for a
  SQL one. `report.suggested_requires` is the whole `requires=` mapping.
- Every exception sverify raises on purpose derives from
  `sverify.errors.SverifyError`, and keeps its built-in base; the classes
  stay importable where they are defined.
- `isin([0, 1])`, and SQL's `x IN (0, 1)`, of integers that fill a range is
  read as that range, so a column known to lie in it meets the condition.

([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691))
