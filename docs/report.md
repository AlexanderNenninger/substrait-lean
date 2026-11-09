# The Report and the trust path

`verify` hands back a report you could give an auditor: what was assumed,
what was proved, what was not and why, and for each engine what the
proof's reach there rests on. This page says what a report holds and how
to follow a verdict to what supports it.

## Proving, before any data

`sv.verify(plan, requires=..., ensures=...)` and `@sv.transform(...)`
prove a plan from its inputs' schemas and the preconditions you state. No
row is read. The result is a `Report`:

```python
report = sv.verify(expr, requires={"orders": [...]}, ensures=[...])
print(report)          # the whole report, as text
report.proved          # True when everything holds
```

A transform whose contract is not proved is refused when it is applied
(`VerificationError`, with the report as `e.report`), unless
`on_unproved="check"` or `"warn"` asks for a run-time check or a warning
instead.

## What a report holds

- The verdict. `report.verdict` is the first line: `proved`, or
  `NOT proved:` and what is missing, counted. `report.proved` is true when
  every postcondition holds, under the observation where `ensures` states
  one, no runtime error is possible, no needed precondition is missing, the
  chosen tolerance is one some engine's doubles actually meet, and, under
  `semantics="substrait"`, the reference's proof carries over.
- The assumptions. `report.requires` lists the preconditions per input
  table, the ones you stated and the ones sverify inferred and assumed;
  `report.assumed` the `SUM`s assumed to fit their type, which the run
  checks on the data; `report.needs` the preconditions the proof needs and
  you have not stated, each with the condition ready for `requires=`.
- The postconditions. `report.ensures` has one entry per postcondition: its
  label, whether it is proved, what the checker found, a counterexample
  where one was found, and the preconditions that would prove it
  (`report.suggestions`).
- The runtime errors. `report.issues` lists the errors the checker could
  not rule out (division by zero, overflow, a bad cast), each with the
  operation and its fix; `report.errors` those an engine fails on.
- What is known about the output. `report.facts` per column, `report.not_null`,
  `report.rows` (a bound on the output's rows from the inputs' row caps).
- The semantics. `report.semantics` is the profile the proof is under
  ([Verifying: the two paths](verifying.md)).
- The observation. `report.observation` is what the result's consumer
  observes: rows as a multiset and doubles within the plan's bound unless
  `ensures` states otherwise with `sv.equivalent(...)`, and it prints the
  bound (`equivalent(floats=plan, ≤ 1.1e-10)`).
- Determinism. `report.deterministic` is false when rows may tie in the
  order of a window, an ordered aggregate or a `LIMIT`: the proof then holds
  for every order of the ties, and `report.notes` names where they stay
  open and the key that would close them.

## Following a verdict to its warrant

Each claim in a report says what it rests on, so a reader can check it
without a search:

- A proved postcondition or a runtime error ruled out rests on the checker's
  run on this plan, and the checker's soundness rests on theorems Lean's
  kernel checks ([the proofs](proofs.md)). [trusted-base.md](trusted-base.md)
  lists everything a result rests on: those theorems, and beyond them the
  parser and writer, the engines' execution and the facts.
- An assumption is named in the report, and checked on the data before
  each run.
- For each engine, `str(report)` prints one `evidence:` line: the plan's
  class on that engine, whether it rests on a proof (`proved by …`) or on
  tests at a pinned engine version (`tested at 2.0.0`), and the engine
  facts behind it, which the [ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)
  list with their evidence.

```text
semantics: reference
evidence: duckdb exact, tested at 2.0.0 (facts duckdb-R6; ...)
evidence: polars exact, proved by ... on polars's model (facts polars-sum-int)
evidence: spark shim, proved by ... on spark's model (facts spark-sum-int, spark-exec-parallel)
```

[How to, Row caps](tasks.md#row-caps) shows such a report in full, with
the names of the proofs.

## Running is separate

A report proves; it runs nothing. `report.run(con, engine)` runs the plan
it checked: it checks the preconditions on the data first, refuses a batch
that breaks one (`PreconditionError`), chooses a route to the engine and
records it in `report.routes`. A report that is not proved is refused
there too (`UnverifiedRunError`) unless `unverified=True` says otherwise.
`report.to_json()` writes the report for another tool, and
`report.to_substrait()` exports the proved plan with its contract.

[How to, Contracts](tasks.md#contracts) shows reports in full, and
[the rejection set](reference-semantics.md#errors) what a report may
refuse.

