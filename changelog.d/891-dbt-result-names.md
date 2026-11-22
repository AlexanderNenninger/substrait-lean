### sverify-dbt's result types take keywords and say statuses in snake_case (breaking)

Before 1.0 freezes them ([#891](https://github.com/AlexanderNenninger/substrait-lean/issues/891) 2.6), sverify-dbt's result types match sverify's. No old name stays as an alias.

- A test's or constraint's `status` is `"pending"`, `"proved"`, `"not_proved"` or `"not_checked"` (`sverify_dbt.result.Status`), where it was `"not proved"` and `"not checked"`. This holds in `TestResult.status`, `ModelResult.by_status(...)` and the tests of each item in `sverify-dbt check --format json`. The text report keeps its words.
- `sverify_dbt.Needed` is `NeededTest`, since `sverify.types.Needed` is another class, and its `because` is `why`.
- `Suggestion.because` (from `CheckResult.suggestions()`) is `Suggestion.why`, a `list[str]`.
- `TestResult`, `NeededTest`, `ContractIssue`, `ModelResult`, `CheckResult` and `Suggestion` take keyword arguments only.
- `CheckResult.tests` and `CheckResult.relations`, the manifest's nodes, are internal (`_tests`, `_relations`).
