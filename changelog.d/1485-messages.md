### Clearer messages: names, vacuous requires, suggestions

An overflow after an aggregate names the measure (`sum(amount) * 2 + 1`) where it
printed Lean's `($1 * 2) + 1`. `sverify check --diff` prints the report's other
fixes (a row cap for an unbounded `SUM`) where no precondition helps, in place of
"No preconditions to add". A report hints at `requires` that no row can meet, such
as `amount > 5` with `amount < 3`, which made every `ensures` hold with nothing to
check. A misspelt column in `requires` or in SQL suggests the closest column.
