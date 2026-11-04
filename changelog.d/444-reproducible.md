### What a rerun must reproduce (#444, D20)

Each output now has two observations: the postcondition's
(`sv.equivalent` in `ensures`), and what a rerun must reproduce, which
the result's consumer states. Sinks take `reproducible=sv.equivalent(...)`
(`DeltaSink`, `IcebergSink` and custom sinks through `Sink.__init__`), with
rows as a multiset and exact values by default, since a sink commits each
epoch once. `refresh(reproducible=...)` and
`Report.run(..., route=..., reproducible=...)` state one for a run; a plain
run requires none and reports determinism. The engine's run-to-run
variation on the options the plan depends on (the `rerun` column of its
choices; for Polars's streaming float `SUM`, within the plan's bound) must
refine it, and a result not determined up to row order fails every
requirement. Otherwise the refresh or run is refused with the reason
(`RouteError`). `deterministic=True` asks for exact values. Where the
tables have no `rerun` for an option, it is read as exact and the route
reports `rerun_evidence="tested"`.
