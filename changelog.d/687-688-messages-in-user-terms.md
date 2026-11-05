### Reports and exceptions in your terms, hints a proof has checked

- A report names each issue by the expression you wrote: Ibis's `//` is one
  issue, `(price - cost) * 100 // price`, where it was ten about the
  reference's rewrite of it; a column computed on the way has its name
  (`ts - lag(ts)`, `sum(amount)`, `mean(temp_c) or std(temp_c)`), never a
  position like `$1`; a cast reads `CAST(amount AS DECIMAL(10, 2))`, an
  interval `ibis.interval(minutes=5)`, and conditions print `datetime(9999, 1,
  1)` where they printed `datetime.datetime(9999, 1, 1, 0, 0)`
  ([#687](https://github.com/AlexanderNenninger/substrait-lean/issues/687)).
- A report's first line is its verdict, `proved` or `NOT proved:` with what
  is missing, counted (`Report.verdict`). A `VerificationError`'s message is
  that count, then one line per finding with its hint, each hint once; the
  full report is `e.report`.
- Route lines lead with the class, in words: `shim (integer division
  rewritten to truncate); evidence proved`, `observed: doubles within
  abs=2e-07; evidence tested`. `Route.reason` keeps the long form.
- The ties note names functions in your transformation's language, and
  messages say "the checker" or "sverify" where they said "Lean".
- `sv.approx` checks its condition when you call it, an Ibis typing error in
  a condition names the condition (`ensures condition 2, …, does not
  type-check`), and a checker built before a change to the Lean sources
  raises `CheckerVersionError` with the command that rebuilds it.
- Every hint carries code a proof has checked, or there is none
  ([#688](https://github.com/AlexanderNenninger/substrait-lean/issues/688)):
  bounds that rule an overflow out are verified again before they are shown;
  a key is suggested on the input it comes from only where it proves the
  output's key, and a key lost through a join says so; a postcondition that
  fails only on a NULL output suggests allowing it
  (`(_.sd_t >= 0) | _.sd_t.isnull()`); the AND/OR hint fires only on an `&`
  or `|` you wrote; the ties note suggests a `unique(...)` only where it
  determines the result.
