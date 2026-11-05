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
- `report.not_null` lists the output columns Lean shows are never NULL, and
  a stored node writes them as NOT NULL columns and records them in its
  contract, with those `ensures` states.
- `report.needed_conditions` gives `report.needs` as conditions ready for
  `requires=`: Ibis deferreds for an Ibis transform, SQL strings for a SQL
  one.
- Every exception sverify raises on purpose derives from
  `sverify.errors.SverifyError`, and keeps its built-in base; the classes
  stay importable where they are defined.
- `isin([0, 1])`, and SQL's `x IN (0, 1)`, of integers that fill a range is
  read as that range, so a column known to lie in it meets the condition.

([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691))
