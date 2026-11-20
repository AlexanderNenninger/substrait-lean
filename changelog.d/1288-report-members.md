### Report: one name for what a proof needs, proved NOT NULL in the output types, the engine version

API changes, with no aliases ([#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288) API-5):

- `CheckedCondition.suggested` (a mapping of conditions per table) is now `CheckedCondition.needs`, a tuple of `Needed` like `Report.needs` and `Issue.needs`. The report JSON writes each as a whole `needed` object, as it writes `Report.needs`.
- `Issue.suggested` is removed: read `Issue.needs`. `on_inferred="silent"` is refused with a `ValueError`: write `"ignore"`.
- `Report.facts` maps each column to a `ColumnFacts` (`nullable`, `lower`, `upper`; `str()` gives the words it held before), in the report JSON too ([#704](https://github.com/AlexanderNenninger/substrait-lean/issues/704)).
- `Report.suggestions` is removed: read `c.needs` of each `c` in `report.ensures`.
- `Report.observation` is removed: `Report.equivalence`, the name every written format already used, is the one name; `Route.observation` is `Route.equivalence`, and a postcondition's `reason` that was `"observation"` is `"equivalence"`, as the report JSON's `ruleId` already said.
- `Report.warnings` is removed. It was always empty; `report.issues` with `error` false is the same list.
- `Report.not_null` is removed: `Report.output` types each column the checker proves never NULL as not nullable (`count(*)` is `!int64`), so `[c for c, t in report.output.items() if not t.nullable]` is the list ([#704](https://github.com/AlexanderNenninger/substrait-lean/issues/704)). The report JSON keeps its `not_null` list, and a report written before reads back with those columns not nullable.

A postcondition proved only with a precondition sverify inferred is no longer reported as proved under `on_inferred="error"`: its `proved` is false, its `reason` is `"needs"` and its `needs` lists the bounds its proof used. A postcondition that holds without them stays proved; `Report.facts` and `Report.output` then rest on the stated preconditions alone. sverify-dbt marks only the tests that used a bound as not proved ([#701](https://github.com/AlexanderNenninger/substrait-lean/issues/701)).

`Report.engine_version` is the engine version the profile of `semantics` describes (`"2.0.0"` under `semantics="duckdb"`), None under the reference; the report JSON carries it ([#710](https://github.com/AlexanderNenninger/substrait-lean/issues/710)).
