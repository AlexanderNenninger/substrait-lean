# The rejection set

The reference raises on a short list of edge cases, the ones where engines
disagree on the answer. Each has a precondition that rules it out, and
sverify works most of them out for you. This page lists them and says how
to read a refusal.

## Where the reference raises

| Kind, as a report names it | When | What rules it out |
|---|---|---|
| `division by zero` | an integer or double `/`, `//` or `%` by zero | a precondition that the divisor is not zero (`_.n != 0`), a filter below the division, or a `CASE` that guards it |
| `overflow` | an integer `+ - *`, negation or `MIN / -1` whose result leaves its declared width | bounds on the inputs (`_.amount < 2**62`), which sverify infers |
| `SUM overflow` | a group's integer `SUM` leaving 64 bits, or a decimal `SUM` leaving its precision | a row cap (`sv.max_rows(n)`) or a bound on the rows per key (`sv.rows_per(...)`) with bounded values; otherwise assumed and checked on the data |
| `overflow to infinity` | an operation on finite doubles, or their `SUM` or `AVG`, giving `±∞` | bounds on the inputs where they prove it finite; otherwise assumed and checked on the data |
| `domain error` | an operation outside its domain: `log` of zero or a negative, `sqrt` of a negative, a NaN an operation would create (`inf - inf`) | a precondition on the argument (`_.x > 0`) |
| `invalid regular expression` | a pattern outside the simple regular expressions the model reads, which may not compile on every engine | a simpler pattern |
| `cast out of range` | a cast of a double to an integer that is NaN, `±∞` or out of range | bounds on the value cast |
| `negative exponent` | an integer power with a negative exponent | a precondition that the exponent is not negative |

A constant that raises, such as `1 // 0` in a later `WHEN`, makes the whole
plan raise on any data: DuckDB evaluates it while it plans the query. No
precondition rules it out; the report says to fix the constant.

[reference-semantics.md](reference-semantics.md#errors) states each case
precisely, and [Options](reference-semantics.md#options) the value each
option takes.

## Preconditions, mostly inferred

You can state every precondition in `requires`. Most you don't have to:
sverify infers the weakest preconditions that rule out each overflow and
each division by zero it can, from the operations the plan runs.

- `on_inferred="error"`, the default: an inferred precondition makes the
  report not proved until you state it, and `report.needs` lists each, with
  the condition ready for `requires=`. A precondition you state is checked
  on each batch before the run, or proved from Delta and Iceberg metadata.
- `"warn"` or `"ignore"`: sverify assumes them, checks them on the data
  before each run, and warns (or doesn't).
- `"off"`: nothing is inferred or assumed; each case is an error that makes
  the report unproved.

A `SUM` that may leave its type, and a double operation that may overflow to
`±∞`, don't block a proof: the report lists them in `report.assumed`, and
the run checks them on the data.

A guard counts only where it holds on every engine. `AND` and `OR` evaluate
both operands, as DuckDB and Polars do, so `(n != 0) & (x // n > 1)` still
needs `n != 0` as a precondition; a `CASE` branch, `NULLIF` or a filter
below the division guards it.

## Under an engine's profile

Under `semantics="duckdb"`, `"polars"` or `"spark"` the plan is checked
against that engine's own profile ([Verifying: the two paths](verifying.md)).
Where the engine's recorded facts show it gives a value the reference raises
on, or raises where the reference gives one, its profile says so, and the
matching precondition still rules the raise out. DuckDB's profile records
its probed double and integer behaviour, and Polars's floors integer `//`
and `%`. An engine's rejection set differs from the reference's only where
its facts record a difference
([the ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)).

## Reading a refusal

A report that is not proved names what is missing, and how to add it:

```text
1 precondition needed (e.report has the details)
  needs: (_.amount < 2**62) on orders, inferred from `amount * 2` (overflow otherwise): declare it in requires ...
```

```text
1 possible runtime error (e.report has the details)
  may fail: division by zero: amount // (amount - 30)
    hint: state `(_.amount != 30)` in the requires of 'orders'
```

State the precondition, or rewrite the plan so no row needs it. A batch
that breaks a stated precondition is refused before anything runs
(`PreconditionError`, with the rows that break it).

