### Suggestions that make a plan verify (#655)

- A postcondition that fails only where a column is NULL (`TRUE or NULL`)
  gets an `IS NOT NULL` precondition on the input column it reads
  (`length(s) >= 0` needs `_.s.notnull()`), inferred and reported under
  `on_inferred` like a bound: listed under `needs:` by default, assumed with
  `"warn"` or `"silent"`. A postcondition that may also be FALSE no longer
  gets the NOT NULL advice.
- A result not determined up to row order names the `sv.unique(...)` that
  determines it, the partition (or grouping) and order columns of its
  windows and ordered aggregates (`Report.ties`); a route refused for a rerun
  carries it in `Route.suggested` and its message.
- A route refused because the plan's bound on doubles exceeds a stated
  tolerance (in `ensures` or `reproducible=`) names the `sv.max_rows(N)`
  under which it fits, the bound growing linearly with the rows, or says
  that no row cap does (`Route.suggested`).
