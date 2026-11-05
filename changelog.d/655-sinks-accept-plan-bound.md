### Doubles into a sink work without extra settings (#655)

A sink's `reproducible` now defaults to rows as a multiset, doubles within
the bound the checker proves for the plan (`Report.epsilon`), and other
values exact: `sv.equivalent(floats="plan")`, the new `floats="plan"`
level. A run whose `ensures` names no observation checks the engine against
the same default, except in the double columns a proved postcondition
reads, which keep their exact value. So a mean into a `DeltaSink` refreshes
on DuckDB and Polars with no `reproducible=` and no `ensures`. A sink whose
consumers need the same bits on a rerun states `reproducible=sv.equivalent()`.
A refusal over a tolerance names the smallest one that passes.
