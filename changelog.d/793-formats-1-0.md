### Breaking changes: the formats' names for 1.0

The three formats take the names 1.x keeps, from the API review's section K
([api-review/PROPOSAL.md](api-review/PROPOSAL.md)). Each is now format 2,
and a reader maps what 0.x wrote
([docs/stability.md](docs/stability.md#the-formats)).

- The sink's contract record names the node `node` (`Contract.node`, for
  `Contract.view`). Delta keeps it under the commit key `sverify.contract`,
  as Iceberg does in its table properties. A Delta table written before
  keeps its records under `sverify`, which `DeltaSource.contract()` and a
  resuming `DeltaSink` still read.
- The Substrait manifest says `semantics`, `equivalence` and
  `equivalence_components` for `profile`, `observation` and
  `observation_components`, and `rows` is an integer. `sv.from_substrait`
  reads exports of format 1.
- The report's JSON says `semantics` in each route and `equivalence` in the
  report and each route. Postconditions, issues and assumptions take the
  shape of a SARIF 2.1.0 result
  ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)):
  `ruleId` (the code in snake_case: `may_be_false`, `division_by_zero`,
  `sum_overflow`), `level` (`error`, `warning`, `note` or `none`, for
  `error: bool`), `kind` (`pass` or `fail`), `message.text`, and sverify's
  fields under `properties`. One `ties` object holds the places and the keys
  that would close them, for `tie_places` and `ties`. Suggested
  preconditions are lists of `needed` objects, under `needs`, for
  `suggested`. The top-level `hints` and an issue's `expr` are gone: each
  issue keeps its `hint` and `shown`. `Report.from_json` refuses format 1,
  which no release wrote.
