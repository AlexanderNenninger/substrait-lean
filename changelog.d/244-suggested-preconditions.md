### Suggested preconditions for unproved postconditions

An unproved postcondition that compares a value with a constant now comes
with the precondition on the inputs under which it holds: `_.doubled <= 100`
with `doubled = qty * 2` reports "would hold with `(_.qty < 51)` in the
requires of 'items'". Sverify proves each suggestion before showing it and
never assumes one. `CheckedCondition.suggested` and `Report.suggestions`
carry them as code, for editors and language servers (#291).
