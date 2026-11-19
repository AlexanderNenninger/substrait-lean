### The oracle of `allows_rows` groups by canonical key

`sverify.testing.lean_choices`, the oracle of `allows_rows`, grouped and deduplicated by exact equality where the reference does it up to canonical codes (D31): keys `-0.0` and `0.0`, or two NaN payloads, gave two groups, each over the whole class's rows, so an engine's single row was rejected. It groups with `distinctRows`, as `Rel.eval` does.
