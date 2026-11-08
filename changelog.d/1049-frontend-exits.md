### SQL and Ibis refusals name their exit; Lean's refusals are `UnsupportedError`

- A plan the checker refuses now raises `UnsupportedError` (still a
  `ValueError`), "substrait-check --contract refuses the plan: …", ending with
  the open coverage issues. Before, the Ibis path raised a plain
  `ValueError`, which `except sverify.errors.SverifyError` missed, and
  `sv.sql`, `Report.to_substrait` and DataFusion worded the same refusal three
  other ways ([#1050](https://github.com/AlexanderNenninger/substrait-lean/issues/1050)).
- The SQL lift names a rewrite or an issue for DISTINCT ON, QUALIFY, named
  windows, LATERAL, PIVOT, SAMPLE, JOIN USING, correlated subqueries,
  WITH RECURSIVE, an aggregate of a DATE at midnight and the SQLGlot
  disagreements SG-4, SG-8 and SG-9; the Ibis producer names #60 or #327 for
  an operation it does not map yet
  ([#1049](https://github.com/AlexanderNenninger/substrait-lean/issues/1049)).
- Unsigned integers and zoned or non-microsecond timestamps name a cast and
  their issues (#350, #323).
