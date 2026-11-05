### Reports and refusals in the user's terms (#655)

- Issues name columns and the Ibis or SQL operator (`total // qty`,
  `sum(x)`, `x / 0`) where Lean's notation said `($3 / $2)` or `$1`, and a
  domain error of a double `SUM` names its cause (NaN from +inf and -inf).
- An inferred precondition says where it came from: `requires t: (_.qty !=
  0) (inferred from total // qty)`, and a batch that breaks it is refused
  with the fix (filter those rows first, a CASE, or state it).
- The AND/OR hint writes out the guard for the user's division; the
  "it comes from it divides by 0" hint names the constant divisor.
- No more "assumes … stays finite" next to "may fail: division by zero"
  for the same operation; the NULL hint names the nullable columns and is
  dropped where none is; an unproved key says to add `sv.unique(...)`.
- An engine setting refuses only where the plan relies on it (a sort's
  NULLS LAST is spelled out, so `default_null_order` warns), and the
  refusal gives the `SET GLOBAL …` that restores it.
- A refused transfer leads with "verify with semantics='reference' to run
  on polars".
- Function refusals use the Ibis or SQL name (`median() or quantile()`,
  `re_extract()`), say which engine runs it and link #271 in full;
  `now()`, `current_timestamp` and `random()` in SQL are refused as
  non-deterministic; the SQL lift quotes the SQL, not SQLGlot's node.
- Refusals name a stored node by its transform (`mean (stored as m)`), and
  the fix for a non-deterministic result is kept on every route.
