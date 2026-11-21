# Sverify next to dbt tests, Great Expectations, Soda and data contracts

These tools check data. Sverify proves a transformation's contract before any
data runs, and checks only what it can't prove. The tools overlap in the rules
they state and differ in when a rule is checked and what it covers, so this
page goes by bug class. Each claim about sverify links to the doc, test or
issue that backs it; [prior work](prior-work.md#related-tools) has the survey
the page condenses.

## What each one checks

| Question | dbt tests | Great Expectations, Soda, Deequ | dbt model contracts and data contracts | sverify |
|---|---|---|---|---|
| When is a rule checked? | After the model builds, on its rows ([dbt data tests](https://docs.getdbt.com/docs/build/data-tests)) | While or after a job runs, on its rows ([prior work](prior-work.md#related-tools)) | At build time, against the schema and constraints ([prior work](prior-work.md#related-tools)) | Before the job runs, for every input that meets the preconditions ([contracts theorems](proved-theorems.md#contracts)) |
| What does a pass say? | These rows pass | These rows pass | The columns and types match | The postcondition holds on every such input |

A rule sverify proves can be left out of `dbt build`: [sverify-dbt](../dbt/README.md#how-a-project-becomes-contracts)
reads a project's tests as preconditions and postconditions and reports which
hold on every run. Many tests hold by construction (`unique` on a `GROUP BY`
key, `not_null` on a filtered column), and those are the cheap ones to prove;
how much a real project saves is [still to be measured](https://github.com/AlexanderNenninger/substrait-lean/issues/1485).

## By bug class

| Bug class | Where a sample-data test falls short | What sverify does |
|---|---|---|
| Late or reversed rows in an incremental job | A watermark job misses a late duplicate and keeps a reversed one | Refreshes from the change feed with delta plans proved equal to a full recompute ([the incremental-view theorems](proved-theorems.md#incremental-view-maintenance); [the tour's first notebook](../notebooks/01_duplicate_payments.py)) |
| Integer overflow, division by zero, bad casts | A test passes until the row that overflows arrives | The proof fails, and the report names the bound to declare ([runtime-error theorems](proved-theorems.md#runtime-errors); [test](../python/tests/test_refresh_overflow.py)) |
| Ties and NaN in windows and sorts | The result depends on the engine's tie order, which sample data rarely shows | The contract is proved `deterministic` or the plan is refused on engines that need it ([window theorems](proved-theorems.md#contracts); [test](../python/tests/test_ties.py); [the tour's second notebook](../notebooks/02_sensor_alerts.py)) |
| Left join NULL padding | A `not_null` or range test on the right side's columns breaks on unmatched rows | The facts a left join keeps and drops are proved ([proved facts](proved-theorems.md#contracts)) |
| Keys that fail after a join or a union | `unique` is sampled | Keys are derived through joins, unions and windows ([key rules](proved-theorems.md#contracts)) |
| One query, different answers on different engines | Each engine's test suite passes on that engine | A plan proved under the reference semantics reaches an engine by a route that names what carries over ([engines and routes](stability.md#engines)) |

## What sverify does not do

- It does not watch the data's behaviour over time: freshness, volume, schema
  drift, upstream duplicates and distribution shifts are not contracts of a
  transformation ([review finding 6](https://github.com/AlexanderNenninger/substrait-lean/issues/1485)).
  Great Expectations, Soda and Deequ stay the tools for them.
- Its preconditions are not proved. They are checked on each batch before the
  run, as dbt's source tests are ([guide](guide.md)).
- It proves what the model states. Tests that hold by construction gain little
  from a proof ([review finding 6](https://github.com/AlexanderNenninger/substrait-lean/issues/1485)).
- Its proofs and code need a human audit before anyone relies on them
  ([README](../python/README.md)).
- It reads a subset of SQL and a subset of Ibis; the rest is refused with the
  construct named ([what the SQL lift reads](reference-semantics.md)).
- It reads DuckDB projects in dbt; singular and unit tests are listed as not
  checked ([sverify-dbt's limits](../dbt/README.md#limits)).

## Using them together

Keep the data checks that watch the data. Add sverify where a transformation's
logic is the risk: a contract the proof covers needs no per-run test of the
same rule, and a rule it can't prove stays a precondition that the run checks.
