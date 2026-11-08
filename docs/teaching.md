# How each feature is taught

Every user-facing feature of sverify and sverify-dbt answers four questions
([#1031]): what it does in one sentence, where a user first meets it, which
tour notebook shows it, and which theorem it rests on. This page holds the
answers, one row per feature, and the refusals with their exits. A missing
answer links to the issue that supplies it.

A pull request that adds or changes a user-facing feature answers the four
questions in its "How do we teach this?" section
([the template](../.github/pull_request_template.md)) and updates its row
here. The table describes main on 2026-11-07. Rows marked "changes with #N"
change when that pull request lands: [#1039] (typed values, D29) and
[#1040] (window sums).

The notebook column names the notebook and its section; "examples" points
to [examples.md](examples.md). The theorem column names the theorem and its
Lean file; [proofs.md](proofs.md) lists each guarantee with its theorem.

## Contracts

| Feature | Sentence | First contact | Notebook | Theorem |
|---|---|---|---|---|
| Contracts: `sv.transform`, `requires`, `ensures` | A rule that ships with a wrong assumption pages someone at 3 a.m.; a contract states what the rule assumes of its inputs and what it promises of its output, and Sverify proves the promise before any data runs. | `@sv.transform(requires=..., ensures=...)`; a promise that is not proved raises `VerificationError`, "N of M postconditions not proved", with the preconditions that would prove it | [04](../notebooks/04_contracts.py), "A first contract" and "When a proof fails"; [01](../notebooks/01_duplicate_payments.py), "2. The rule and its contract" | `contract_sound`, `contract_sound_all` ([Contracts.lean](../SubstraitLean/Contracts.lean)) |
| Checking without running: `sv.verify`, `transform.check` | You want to know whether a rule holds before you point it at production; Sverify checks a contract against schemas alone and returns a `Report`. | `sv.verify(expr, requires=, ensures=)` returns the report; `paid.check(orders=schema)` returns it without raising; `str(report)` reads it line by line | [02](../notebooks/02_sensor_alerts.py), "2. The rule, and the first thing the checker says"; [03](../notebooks/03_orders_mart.py), "2. The model, and its tests as a contract" | `contract_sound` ([Contracts.lean](../SubstraitLean/Contracts.lean)) |
| Unproved plans are refused: `on_unproved` | A rule that was never proved should not reach your tables unnoticed; Sverify refuses to run a plan it could not prove unless you ask it to check the promise on the data. | `UnverifiedRunError`, "refused on E: not verified", naming `unverified=True` and `on_unproved="check"` or `"warn"` | [04](../notebooks/04_contracts.py), "Contracts on real data" | The checker is trusted glue over `contract_sound` and `Rel.keys_sound` ([proofs.md, What is trusted](proofs.md#what-is-trusted)); no theorem row: [#1057] |
| Inferred preconditions: `on_inferred` | An overflow or a division by zero deep in a rule breaks the run long after review; Sverify infers the bound each step needs and asks you to state it in `requires`. | The report's `needs:` line, "declare it in requires", with `on_inferred="warn"` as the other exit; at run time, `PreconditionError`, "refused before the run. The precondition was inferred from ..." | [04](../notebooks/04_contracts.py), "Guards"; [01](../notebooks/01_duplicate_payments.py), "2. The rule and its contract" (where each precondition comes from) | `Rel.mayIssues_sound` ([Safety.lean](../SubstraitLean/Safety.lean)), `Rel.issuesCapped_sound` ([Rows.lean](../SubstraitLean/Rows.lean)) |
| Runtime errors and guards | A guard you wrote in an `AND` may not protect the division beside it, because engines evaluate both sides; Sverify reports each possible runtime error with the guard that removes it. | `report.errors`; "may fail: division by zero", with a `hint:` naming the precondition or the `CASE` | [04](../notebooks/04_contracts.py), "Runtime errors" and "Guards" | `Rel.guardFree_sound` ([Guards.lean](../SubstraitLean/Guards.lean)), `Rel.mayIssues_sound` ([Safety.lean](../SubstraitLean/Safety.lean)) |
| Keys: `sv.unique`, `sv.key` | A key that stops being unique double-counts revenue in every report downstream; Sverify proves which keys survive a rule and checks the input's keys on each batch. | `sv.unique("id")` in `requires` or `ensures`; a batch with a duplicate raises `PreconditionError`, "N row(s) of t violate unique(id)", which names no exit ([#1057]) | [04](../notebooks/04_contracts.py), "Keys"; [02](../notebooks/02_sensor_alerts.py), "6. New readings, and a sensor that sends twice". `sv.key` in no notebook: [#1057] | `Rel.keys_sound`, `Rel.keys_sound_all` ([Keys.lean](../SubstraitLean/Keys.lean)) |
| Foreign keys: `sv.references` | An order whose customer is missing turns into a NULL in the mart; Sverify takes a foreign key as a precondition and uses it to prove what a join keeps. | `sv.references("customer_id", to=customers.id)` in `requires`; the report's `requires` line | Text only in [04](../notebooks/04_contracts.py), "Keys": [#1057] | `Rel.fkMatch_sound` ([Semantic.lean](../SubstraitLean/Semantic.lean)), for rewrites; no row in proofs.md: [#1057] |
| Row caps: `sv.max_rows`, `sv.rows_per` | A sum of a billion rows overflows 64 bits where a sum of a thousand does not; a row cap tells Sverify how many rows to expect, and the bounds it proves follow from it. | The `hint:` of a `SUM` names a cap or a bound; `requires: max_rows(N)` in the report, and "rows: at most N" under "known about the output" | Text only in [03](../notebooks/03_orders_mart.py), "2. The model, and its tests as a contract"; examples 5 and 6: [#1057] | `Rel.maxRows_sound` ([Contracts.lean](../SubstraitLean/Contracts.lean)), `Rel.issuesCapped_sound` ([Rows.lean](../SubstraitLean/Rows.lean)); no row for `max_rows`: [#1057] |
| Composing contracts | A rule downstream trusts what the one upstream promised, so a change upstream can break it silently; Sverify checks each link and reports the promise the consumer needs. | The consumer's `requires paid:` lines; a broken link raises `CompositionError`, which names no exit ([#1057]) | [04](../notebooks/04_contracts.py), "Composing contracts" and "When the link breaks" | `contract_sound` per link; `Rel.chain_sound`, `Rel.stack_sound` for refresh ([Compose.lean](../SubstraitLean/Compose.lean)) |

## Doubles, observations and ties

| Feature | Sentence | First contact | Notebook | Theorem |
|---|---|---|---|---|
| Observations: `sv.equivalent` and the float default | Two engines sum doubles in different orders, and the last digits differ; an observation says what the result's consumer looks at, and Sverify accepts every result equal to a proved one up to it. | `ensures=[sv.equivalent(rows=..., floats=...)]`; without it, `report.observation` prints `equivalent(floats=plan, ≤ ε)`, the plan's bound. A window aggregate of doubles has no bound yet; changes with [#1040] | Text only in [05](../notebooks/05_pipelines_and_engines.py), "Routes: how a proof reaches an engine"; example 5: [#1045] | `Relation.Equiv_mono` ([ObsEquiv.lean](../SubstraitLean/ObsEquiv.lean)), `Rel.plan_near` ([Lipschitz.lean](../SubstraitLean/Lipschitz.lean)), `StdModel.epsilon_sum_cr` ([float-bounds Epsilon.lean](../float-bounds/FloatBounds/Epsilon.lean)); statistics (D30) rest on `StdModel.core_var_chan` ([float-bounds Chan.lean](../float-bounds/FloatBounds/Chan.lean)) |
| Tolerance: `sv.within`, `sv.approx` | A threshold of 100 on a mean that is only within 1e-4 of the true value can flip a row; `sv.approx` lets Sverify allow for the tolerance and still prove the postcondition. | `floats=sv.within(abs=..., rel=...)`; a route reason "write it as sv.approx(...)" or "state sv.equivalent(floats=...)". A column without a bound is treated more leniently than one with a bound: [#1045] | No notebook: [#1045] | `Expr.narrow_sound`, `Expr.robust_of_depends` ([Robust.lean](../SubstraitLean/Robust.lean)), `contract_sound_allowed` ([AllowedNear.lean](../SubstraitLean/AllowedNear.lean)); `approxWithin` has no theorem: [#1045] |
| NaN, infinities and one zero | A NaN from a broken sensor passes `> 30` in DuckDB and not in Python; Sverify models NaN as DuckDB does under `semantics="duckdb"` and proves which rows it reaches. | `~_.x.isnan()` in `requires`; the report's facts on a double column | [02](../notebooks/02_sensor_alerts.py), "3. The NaN glitch"; [05](../notebooks/05_pipelines_and_engines.py), "Doubles: NaN, infinities and one zero" | `Rel.allowed_duckdb_core` ([EngineTables.lean](../SubstraitLean/EngineTables.lean)) |
| Ties and `reproducible=` | A window over tied timestamps picks a different row on each rerun, and the alert fires twice; Sverify names each tie that stays open and the key that closes it, and `reproducible=` refuses a plan whose ties are open. | `report.deterministic`, `report.ties` with the `sv.unique(...)` to add; `reproducible=sv.equivalent()` raises `RouteError`, "a rerun must give the same result: ... ties stay open at ..." | [02](../notebooks/02_sensor_alerts.py), "2. The rule, and the first thing the checker says"; [04](../notebooks/04_contracts.py), "Ties". `reproducible=` in no notebook: [#1048] | `Rel.window_deterministic` ([Keys.lean](../SubstraitLean/Keys.lean)), `Rel.orderAllowed_allowed` ([Ties.lean](../SubstraitLean/Ties.lean)); no row for the deterministic profile: [#1048] |

## Engines and SQL

| Feature | Sentence | First contact | Notebook | Theorem |
|---|---|---|---|---|
| Routes and classes: `route="auto"` | A proof made under one semantics says nothing about an engine with another unless something carries it over; a route is that carrier, and its class tells you what you can rely on. | `report.run(con, engine, route="auto")`, `report.routes[engine]`: "exact", "observed", "shim" or "refused", with the evidence; `RouteError` names the options that differ. An explicit `route=` refusal names no exit: [#1046] | [05](../notebooks/05_pipelines_and_engines.py), "Routes: how a proof reaches an engine" | `Lowering.lowerRel_sound` ([Lowering.lean](../SubstraitLean/Lowering.lean)), `Rel.duckdb_refines` ([Obligations.lean](../SubstraitLean/Obligations.lean)), `Rel.polars_sound` ([PolarsShims.lean](../SubstraitLean/PolarsShims.lean)), `Rel.spark_sound` ([SparkShims.lean](../SubstraitLean/SparkShims.lean)), `Rel.AllowedP_transfer` ([Transfer.lean](../SubstraitLean/Transfer.lean)); no row per class: [#1046] |
| Profiles: `semantics=` | Your engine rounds, divides and orders by its own rules; a profile states those rules, and Sverify can prove a plan under the engine's own profile or under its strict reference. | `sv.verify(..., semantics="duckdb" \| "polars" \| "spark" \| "substrait")`; the report's `semantics:` line | Examples 7 to 9; no notebook: [#1046] | `Rel.allowed_duckdb_core`, `Rel.allowed_polars_core` ([EngineTables.lean](../SubstraitLean/EngineTables.lean)), `Rel.allowed_substrait_core` ([SubstraitProfile.lean](../SubstraitLean/SubstraitProfile.lean)) |
| Engines: DuckDB, Polars, Spark, Snowflake | One plan, proved once, runs where your data lives; [stability.md, Engines](stability.md#engines) says which engines and how. | `refresh(engine=...)`, `report.run(con, engine)`; a function only DuckDB runs is refused with "run it with engine='duckdb' (see #271)". Each engine refusal names `engine="duckdb"` or a rewrite | [01](../notebooks/01_duplicate_payments.py), "3. One plan, every engine"; [05](../notebooks/05_pipelines_and_engines.py), "Choosing the engine for a node". Spark runs in no notebook: [#1047] | As for routes; Snowflake's profile is [#851], from Snowflake behaviour recorded privately |
| SQL for an engine: `to_sql` | Your warehouse runs SQL, and a hand translation loses the proof; Sverify writes the proved plan as DuckDB, Spark or Snowflake SQL. | `report.to_sql(dialect)`; `UnsupportedError` for a window with open ties, naming `deterministic=`; the other writer refusals name `engine="duckdb"` | [02](../notebooks/02_sensor_alerts.py), "5. Every engine, and the warehouses"; [05](../notebooks/05_pipelines_and_engines.py), "SQL for DuckDB, Snowflake and Spark" | `Lowering.lowerRel_sound` for DuckDB; `Rel.spark_sound` for Spark; Snowflake waits on [#851] |
| Engine settings and versions | An engine upgraded or reconfigured behind your back can change what a proof assumed; Sverify checks the engine's version and settings before it runs. | `EngineVersionError`, "install a N.x release"; `EngineSettingsError`, "restore it with `SET ...`" | No notebook: [#1056] | The engine facts the profile rests on ([characterization/README.md](../characterization/README.md)) |
| SQL in sverify: `sv.sql`, `verify` of a SQL string | Half your rules are SQL already; Sverify reads DuckDB SQL into the same plan an Ibis expression gives and proves it the same way. | `sv.verify("SELECT ...", tables=...)`, `.pipe(sv.sql(query))`; `UnsupportedError` for what the lift does not read yet, often with no exit: [#1049] | [03](../notebooks/03_orders_mart.py), "The same model in SQL". `sv.sql` in no notebook: [#1049] | The `agree` field of each `LiftEntry` ([LiftSearch.lean](../SubstraitLean/LiftSearch.lean)); no row in proofs.md: [#1049] |
| Typed values and kinds | A decimal added to a double, or a scale that silently drops a cent, is a wrong answer that looks right; Sverify checks each expression's kind and refuses a mix it cannot type. Changes with [#1039] | A Lean refusal reaches you as a plain `ValueError`, "substrait-check --contract failed: ..."; unsigned integers and zoned timestamps are refused without an exit: [#1050] | No notebook: [#1050] | `Rel.kinds_sound`, `Expr.kindT_sound` ([Kinds.lean](../SubstraitLean/Kinds.lean)) |
| Timestamps and intervals | A month bucket of a timestamp near the year 1 or 9999 overflows; Sverify bounds the timestamps a truncation needs and reads intervals in the units it models. | The report's `needs:` for a timestamp bound; "interval of days or months is not modelled yet (#342); write it in hours or seconds" | [05](../notebooks/05_pipelines_and_engines.py), "Timestamps and intervals" | `Rel.mayIssues_sound` ([Safety.lean](../SubstraitLean/Safety.lean)) |
| `sv.asof_join` | A trade matched to a quote from after it is a look-ahead bug; `sv.asof_join` matches each row with the latest earlier row of another table, and Sverify checks the join's tolerance. | `sv.asof_join(left, right, on=, by=, tolerance=, how=)`; "only ASOF [LEFT] JOIN", "needs an ON condition" | [04](../notebooks/04_contracts.py), "ASOF joins" | No theorem: [#1052] |
| `sv.connect` | You want to try a contract on a few rows before wiring a pipeline; `sv.connect` holds named in-memory tables for Ibis expressions. | `con = sv.connect(); con.create(...)` or `con.put(...)` | [04](../notebooks/04_contracts.py), "Contracts on real data" | It holds data and makes no claim |

## Pipelines

| Feature | Sentence | First contact | Notebook | Theorem |
|---|---|---|---|---|
| Nodes and refresh: `.pipe`, `.write`, `refresh`, `group`, `status` | Recomputing the whole table every hour costs money, and a hand-written incremental job drifts; Sverify keeps each node up to date from its sources' changes and proves the result equals a recomputation. | `node.refresh()` prints what changed per source; `node.status()` says what is maintained and what is recomputed; `NotIncrementalError` and the incremental limits name no exit: [#1051] | [01](../notebooks/01_duplicate_payments.py), "4. New transactions"; [05](../notebooks/05_pipelines_and_engines.py), "Keeping a join up to date" and "Pipelines" | `Rel.delta_correct`, `Rel.incremental_sound` ([Incremental.lean](../SubstraitLean/Incremental.lean)), `Refresh.no_corruption` ([Refresh.lean](../SubstraitLean/Refresh.lean)); the TLA+ model ([models/refresh](../models/refresh/README.md)) has no row: [#1051] |
| `sverify.io.Changes`, `StaticSource` | You want to test a pipeline's refresh without a lake; a `StaticSource` is an in-memory table with versions, and `Changes` is a batch of inserts and deletes for it. | `StaticSource(...)`, `source.apply(Changes(...))`; deleting a row that is not there raises `ValueError` | [05](../notebooks/05_pipelines_and_engines.py), "Keeping a join up to date" | `Rel.delta_correct` ([Incremental.lean](../SubstraitLean/Incremental.lean)) |
| Sources and sinks: Delta, Iceberg, Flight, your own | The contract a job proved is lost the moment its result lands in a table; a sink stores the result exactly once per state with its contract, and the next job reads both. | `.write(DeltaSink(...))`, `DeltaSource(...).contract()`; "has constraints the view does not guarantee" names no exit: [#1048] | [01](../notebooks/01_duplicate_payments.py), "5. The sink carries the contract"; [02](../notebooks/02_sensor_alerts.py), "6. New readings"; [05](../notebooks/05_pipelines_and_engines.py), "Your own source and sink" | `Rel.cdf_sound` ([TableFormat.lean](../SubstraitLean/TableFormat.lean)), `Refresh.no_corruption` ([Refresh.lean](../SubstraitLean/Refresh.lean)) |
| A sink's float default: `reproducible=` | A rerun that writes different last digits rewrites every downstream table; a sink's `reproducible=` says how close two writes must be, `floats="plan"` by default. | `DeltaSink(..., reproducible=sv.equivalent(...))`; `RouteError` names the observation that would do | Example 6; no notebook: [#1048] | `Rel.plan_near` ([Lipschitz.lean](../SubstraitLean/Lipschitz.lean)); no row: [#1048] |
| Quarantine and hold: `on_violation` | One bad row should not stop the whole refresh or slip into the result; Sverify sets the rows that break a precondition aside and refreshes the rest. | `on_violation="quarantine"` or `"hold"`; the refresh prints "N row(s) quarantined" with the condition each broke | [05](../notebooks/05_pipelines_and_engines.py), "When the data breaks the contract" | `Catalog.kept_sound` ([Quarantine.lean](../SubstraitLean/Quarantine.lean)) |
| Time buckets: `sv.arrives_within` | State that grows with every hour of history eventually takes the job down; a lateness bound lets Sverify retire old buckets and prove the result stays the same. | `sv.arrives_within(...)` in `requires`; the refresh's "retention ... N bucket(s) open" line | No notebook: [#1056] | `retention_sound`, `expiry_sound` ([Retention.lean](../SubstraitLean/Retention.lean)) |
| Credentials: `Secret`, `Resolver` | A key pasted into a pipeline file leaks with the repository; Sverify names each credential by where it lives and reads it when a table opens. | `Secret("env:NAME")`; `node.credentials()` lists them per table | No notebook: [#1056] | It reads secrets and makes no claim |
| OpenLineage | Your catalog wants to know which job wrote which table under which contract; Sverify emits a run per node on each refresh, with the contract in its `sverify_contract` facet. | The guide's [OpenLineage](guide.md#openlineage) section | No notebook: [#1056] | It reports and makes no claim |
| Sharding: `run_sharded` | A plan too large for one machine runs in pieces, and pieces of a double sum round differently; Sverify proves which plans split exactly and bounds the ones that do not. | `NotShardable` names its exit, `float_order="any"`, which `run_sharded` deprecates: [#1054] | No notebook: [#1054] | `StdModel.sharded_near` ([float-bounds Shard.lean](../float-bounds/FloatBounds/Shard.lean)), `Rel.optimize_sound` ([Semantic.lean](../SubstraitLean/Semantic.lean)) |

## Contracts for others and tools

| Feature | Sentence | First contact | Notebook | Theorem |
|---|---|---|---|---|
| Substrait export: `to_substrait`, `from_substrait`, `substrait_contract` | Another team's engine should run your plan with the same guarantees; Sverify writes the proved plan as Substrait with the conditions its proof needs. | `report.to_substrait(format=...)`; `ExportError` with `shims="annotate"` as its exit, and some kinds with no exit: [#1053] | Example 10; no notebook: [#1053] | The writer is trusted and checked by a round trip; `declared_rows` ([Write.lean](../SubstraitLean/Write.lean)) covers declarations only: [#1053] |
| ODCS contracts | A data contract in a standard format lets another team build on your table; Sverify writes the proved contract as ODCS. | The guide's [ODCS contracts](guide.md#odcs-contracts) section | No notebook: [#1053] | No theorem: [#1053] |
| The `sverify` command | You want the proof in CI and on the pull request, without a notebook; `sverify check` proves every transform and node in a file and prints the contract in plain words. | `sverify check file.py --diff` and `--fix`; each finding carries a code that `sverify explain` describes; "time budget exceeded" does not name `SVERIFY_TIMEOUT`: [#1056] | No notebook: [#1056] | `contract_sound` ([Contracts.lean](../SubstraitLean/Contracts.lean)) for what it reports |
| The pytest plugin | A contract belongs in the test suite you already run; the plugin's `assert_contract(node)` asserts a node's contract is proved and, with rows, checks it on them. | The guide's [Testing with pytest](guide.md#testing-with-pytest) section | No notebook: [#1056] | `contract_sound` ([Contracts.lean](../SubstraitLean/Contracts.lean)) |
| sverify-dbt | A dbt test that always holds still costs a query on every build; Sverify-dbt proves a project's tests from the tests upstream and lists those `dbt build` can skip. | `sverify-dbt check`, `suggest`, `--selectors`; the report's `needs` lists the source test to add; several model refusals name no exit: [#1055] | No notebook: [#1055]. [03](../notebooks/03_orders_mart.py) proves dbt-style tests with sverify itself | `contract_sound`, `Rel.keys_sound` under `semantics="duckdb"`; not named in [dbt/README.md](../dbt/README.md): [#1055] |

## Refusals and their exits

Every refusal sverify gives today, grouped by family, with what the user
does next. A family whose message names no exit links to the issue that
adds one. The inventory reads `python/src/sverify` and `dbt/src/sverify_dbt`
on 2026-11-07.

| Refusal | Feature | Exit |
|---|---|---|
| `VerificationError`, "N of M postconditions not proved" | Contracts | The preconditions that would prove it, when the checker finds them; `on_unproved="check"` |
| `CompositionError`, "{consumer} needs ...; {producer} only guarantees ..." | Composition | None: [#1057] |
| `VerificationError`, a `needs:` line | Inferred preconditions | State it in `requires`, filter, `CASE`, or `on_inferred="warn"` |
| `PreconditionError`, an inferred precondition broken by a batch | Inferred preconditions | `t.filter(...)`, `CASE`, or state it |
| `PreconditionError`, a stated precondition, key, `max_rows` or `arrives_within` broken by a batch | Contracts, pipelines | None; `on_violation` is not named: [#1057] |
| `PreconditionError`, an assumed `SUM` or `±inf` broken by a batch | Contracts | None: [#1057], lifted by [#575] |
| `UnverifiedRunError`, "refused on E: not verified" | Unproved plans | `unverified=True`; for refresh, `on_unproved="warn"` |
| `RouteError`, "verify with semantics='reference' to run on E" | Routes | `semantics="reference"` |
| `RouteError` for an explicit `route=` that does not apply | Routes | None: [#1046] |
| "this checker cannot check under semantics=X yet" | Profiles | None named: [#1046], lifted by [#444] step 3a |
| An option of class `refused` in an engine's table | Routes | The facts; no table row is `refused` today: [#1046] |
| "E agrees with the reference only up to q" | Observations | State it in `sv.equivalent(...)` |
| "the postcondition X reads c, which is within ..." | Tolerance | `sv.approx(X)` or `sv.equivalent(floats=...)` |
| "c is within ...", a stated `within` the bound does not meet | Tolerance | A looser tolerance, or `sv.max_rows(N)` |
| "c has no bound on its distance to the reference" | Tolerance | `floats="plan"` or drop the tolerance; lifted by [#1032] and [#85] |
| "a filter, grouping key or sort on a double may keep other rows" | Tolerance | A precondition away from the threshold; refuses the whole plan: [#1045] |
| "observes the rows as a sequence, and the plan's result is not sorted" | Observations | None: [#1045] |
| "a rerun must give the same result: ... ties stay open at ..." | Ties | `sv.unique(...)` in `requires`, or an `order_by` before `LIMIT` |
| "two runs on E agree only up to ..." | `reproducible=` | `reproducible=sv.equivalent(floats=...)` |
| `EngineVersionError` | Engine versions | Install the named release |
| `EngineSettingsError` | Engine settings | `SET ...` as named |
| `RouteError`, "N node(s) of the streaming plan run on the in-memory engine" | Polars | `streaming=` other than `"require"` |
| "X runs on duckdb only (see #271)" | Engines | `engine="duckdb"`; lifted by [#271] |
| Spark and Snowflake date guards; DataFusion's NTILE | Engines | `engine="duckdb"`; lifted by [#271] and DF-11 |
| "run on polars only; E truncates" | Profiles | `semantics="reference"` |
| A DuckDB-only construct on another writer (TRY_CAST, lists, black boxes, ...) | SQL for an engine | `engine="duckdb"`; lifted by [#271] |
| "the E writer does not write integer division yet" and other writer hooks | SQL for an engine | `engine="duckdb"`; lifted by [#271] |
| "the E writer does not write overflow = X yet" | SQL for an engine | `engine="duckdb"`; lifted by [#241] |
| "tables have no row order" on Spark | SQL for an engine | `deterministic=True` |
| "window functions need an ORDER BY" on Spark and Snowflake | SQL for an engine | `engine="duckdb"`; lifted by [#271] |
| Spark's LN, POWER, ATAN2 | Engines | `engine="duckdb"` (spark-elem-rounding) |
| Spark decimals past 38 digits | Engines | Cast an operand to fewer digits |
| Spark decimal negation, division, double to DECIMAL | Engines | A cast to fewer digits (to DOUBLE for an AVG), or `engine="duckdb"`; lifted by [#27] |
| Snowflake's libm, MOD, VAR, decimals, intervals | Engines | `engine="duckdb"`; Snowflake behaviour recorded privately; lifted by [#852] |
| "Snowflake SQL is written only for plans verified under the reference" | SQL for an engine | `semantics="reference"` |
| DataFusion's AVG of integers, substring | Engines | `engine="duckdb"` (DF-24, DF-23) |
| Polars decimals, categorical strings, type mismatches, refused functions | Engines | `engine="duckdb"`, which every Polars refusal names |
| "unsigned integers are not supported", zoned timestamps | Typed values | None: [#1050], lifted by [#350] and [#323] |
| float32, "use float64"; nanosecond times, "cast them to microseconds" | Typed values | As named |
| "substrait-check --contract failed: ..." | Typed values, frontends | Lean's message, often none: [#1050] |
| "the checker refuses the SQL: ..." | SQL in sverify | Lean's message |
| "cannot parse the SQL as DuckDB's", "only SELECT queries are" | SQL in sverify | None: [#1049] |
| An alias clash (SG-1), `~` (SG-10), `t.*` with USING (SG-5) | SQL in sverify | Rename, `regexp_matches`, list the columns |
| Underscores in numbers (SG-4), `ago` (SG-8), EXPORT_STATE (SG-9), NULL order | SQL in sverify | None: [#1049] |
| WITH RECURSIVE, DISTINCT ON, named windows, correlated subqueries, JOIN USING, UNPIVOT | SQL in sverify | None: [#1049] |
| A CAST that rounds in DuckDB, `mode()` ties, `median` of DECIMAL | SQL in sverify | `semantics="reference"` or `round()`, an order, a cast to DOUBLE |
| An aggregate of a DATE at midnight | SQL in sverify | None named; lifted by [#240]: [#1049] |
| "interval of days or months is not modelled yet" | Timestamps | Write it in hours or seconds; lifted by [#342] |
| `ibis.now()`, random, row ids, hashes, `approx_*` | Contracts | Pass the value in |
| An unbound Ibis parameter | Contracts | `params={param: value}` ([#354]) |
| Other Ibis operations: translate, array_value, lambdas, typeof | SQL in sverify | None: [#1049], lifted by [#60] and [#327] |
| ASOF joins other than ASOF [LEFT] JOIN, or without ON | `asof_join` | Rewrite as named |
| `NotIncrementalError` | Refresh | None: [#1051] |
| "conditions on derived inputs were not proved", foreign keys in views, checked preconditions on views | Refresh | None: [#1051] |
| "batches are not checked against rows_per yet" | Refresh | None named; lifted by [#219] |
| `SchemaError` | Refresh | Build the pipeline again |
| `AuditError` | Refresh | None: [#1051] |
| A fused `on_unproved="check"` node; `refresh()` under `sverify check` | Refresh | `.write(sink)` first; `if __name__ == "__main__":` |
| A view over tables without a source; a changed static table; a newer contract format | Sources and sinks | `StaticSource(...)`, a new version, upgrade sverify |
| A Delta table with constraints the view does not guarantee | Sources and sinks | None: [#1048] |
| `ExportError`, "refused for Substrait" | Export | `shims="annotate"` |
| `ExportError`, a relation kind or a function outside Substrait's YAMLs | Export | A gap id only: [#1053] |
| `NotShardable` for a SUM or AVG of doubles | Sharding | `float_order="any"`, deprecated: [#1054] |
| sverify-dbt: not a DuckDB project; no manifest | sverify-dbt | [#271]; `dbt compile` |
| sverify-dbt: an unmapped test, a foreign key of a result, a Python model, a table that is no ref or source, unplannable SQL | sverify-dbt | None: [#1055] |
| `sverify check`: "time budget exceeded" | The `sverify` command | None; `SVERIFY_TIMEOUT` is not named: [#1056] |

[#27]: https://github.com/AlexanderNenninger/substrait-lean/issues/27
[#60]: https://github.com/AlexanderNenninger/substrait-lean/issues/60
[#85]: https://github.com/AlexanderNenninger/substrait-lean/issues/85
[#219]: https://github.com/AlexanderNenninger/substrait-lean/issues/219
[#240]: https://github.com/AlexanderNenninger/substrait-lean/issues/240
[#241]: https://github.com/AlexanderNenninger/substrait-lean/issues/241
[#271]: https://github.com/AlexanderNenninger/substrait-lean/issues/271
[#323]: https://github.com/AlexanderNenninger/substrait-lean/issues/323
[#327]: https://github.com/AlexanderNenninger/substrait-lean/issues/327
[#342]: https://github.com/AlexanderNenninger/substrait-lean/issues/342
[#350]: https://github.com/AlexanderNenninger/substrait-lean/issues/350
[#354]: https://github.com/AlexanderNenninger/substrait-lean/issues/354
[#444]: https://github.com/AlexanderNenninger/substrait-lean/issues/444
[#575]: https://github.com/AlexanderNenninger/substrait-lean/issues/575
[#851]: https://github.com/AlexanderNenninger/substrait-lean/issues/851
[#852]: https://github.com/AlexanderNenninger/substrait-lean/issues/852
[#1031]: https://github.com/AlexanderNenninger/substrait-lean/issues/1031
[#1032]: https://github.com/AlexanderNenninger/substrait-lean/issues/1032
[#1039]: https://github.com/AlexanderNenninger/substrait-lean/pull/1039
[#1040]: https://github.com/AlexanderNenninger/substrait-lean/pull/1040
[#1045]: https://github.com/AlexanderNenninger/substrait-lean/issues/1045
[#1046]: https://github.com/AlexanderNenninger/substrait-lean/issues/1046
[#1047]: https://github.com/AlexanderNenninger/substrait-lean/issues/1047
[#1048]: https://github.com/AlexanderNenninger/substrait-lean/issues/1048
[#1049]: https://github.com/AlexanderNenninger/substrait-lean/issues/1049
[#1050]: https://github.com/AlexanderNenninger/substrait-lean/issues/1050
[#1051]: https://github.com/AlexanderNenninger/substrait-lean/issues/1051
[#1052]: https://github.com/AlexanderNenninger/substrait-lean/issues/1052
[#1053]: https://github.com/AlexanderNenninger/substrait-lean/issues/1053
[#1054]: https://github.com/AlexanderNenninger/substrait-lean/issues/1054
[#1055]: https://github.com/AlexanderNenninger/substrait-lean/issues/1055
[#1056]: https://github.com/AlexanderNenninger/substrait-lean/issues/1056
[#1057]: https://github.com/AlexanderNenninger/substrait-lean/issues/1057
