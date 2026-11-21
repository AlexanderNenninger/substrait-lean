# Checking without running, and the command line

The examples on this page run in order (`python/tests/test_readme.py`), from this setup:

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))  # now orders holds bob and cy
```

## Checking without running

A tool that reads a contract's proof, such as an editor, a CI step or dbt,
checks a transform on input schemas with `check`. It returns the report
without raising and reads no data, so `requires` is not checked on a bound
table:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.unit >= 0])
def unit_price(orders):
    return orders.select(orders.id, unit=orders.amount // orders.qty)


report = unit_price.verify(orders={"id": "int64", "amount": "int64", "qty": "int64"})
print(report.verdict == sv.Verdict.PROVED, [n.label for n in report.needs])
# False ['(_.qty != 0)']
print(report.ensures[0].message)
# NOT proved: it may be FALSE or NULL on some rows
print(report.route("duckdb").cls)
# refused
```

The report's parts come as data and as the lines `str(report)` prints:

- `Report.inputs` and `Report.output` give the schemas of the input tables
  and of the result, the columns `requires` and `ensures` may name.
- `CheckedCondition.message`, `Issue.message`, `Issue.assumption` and
  `Report.notes` are the report's lines for each postcondition, possible
  runtime error, assumption and note.
- `Report.needs` gives the preconditions the proof needs, one `Needed` each:
  table, column, comparison, bound, SQL, the runtime error it rules out,
  the fixes in words (`text`) and the `condition` ready for `requires=`, in
  the transform's language: an Ibis deferred (`_.qty.isnull() | (_.qty != 0)`,
  NULL passing as the inferred bound lets it) or a SQL string.
  `Issue.needs` holds the same records for one runtime error, which
  `Issue.hint` states in words.
- `Report.suggested_requires` is the whole `requires=` mapping: the stated
  preconditions and the inferred ones, ready to pass to `verify` again or
  to paste into the decorator.
- `Report.route(engine)` gives the route a run would take and the plan's
  class on the engine (exact, observed, shim or refused) without running
  it. After a run, `report.routes` records the route taken.
- `report.to_json()` writes the report as a versioned JSON document for CI
  jobs and tools: the verdict, each postcondition with its reason and
  counterexample, the issues, the needs, the facts and the routes, in the
  format of [`report.schema.json`](../python/src/sverify/schemas/report.schema.json).
  Postconditions, issues and assumptions are findings in the shape of a
  SARIF result, with a `ruleId`, a `level` and a `message`.
  `sv.Report.from_json(text)` reads it back into a `Report` with the same
  verdict ([stability](stability.md)).

The counterexample search tries 200 inputs per unproved postcondition. The
`SVERIFY_COUNTEREXAMPLES` environment variable sets that budget for
`sv.verify`, a transform's call and `check`; 0 skips the search, for a tool
that only needs the verdicts
([test_check_api.py](../python/tests/test_check_api.py)). It skips a
postcondition that only the order of ties leaves open: the checker proves
it where every window orders its rows totally, so its reason is `"ties"`
(`CheckedCondition.ties`), and a key that breaks the ties proves it
([test_checker_speed.py](../python/tests/test_checker_speed.py)).

Sverify keeps the checker's answers on disk, so the next `verify`, `check`
or `refresh` of an unchanged transform takes its proof from there, and an
edit proves again only the transforms whose plans, conditions or inputs
changed.
An entry is keyed by what the checker reads (the plans, the conditions and
the profile), sverify's version and a hash of the checker binary, so a
change to any of them proves again
([test_proof_cache.py](../python/tests/test_proof_cache.py)). The cache is
in `SVERIFY_CACHE_DIR`, else `$XDG_CACHE_HOME/sverify`, else
`~/.cache/sverify`; processes share it. `SVERIFY_CACHE_DIR` moves the cache
and `SVERIFY_CACHE=off` (or `0`, `false`, `no`) turns it off; the two are
independent, and `off` wins when both are set. Within a Python process or a command, one checker process answers
every request. A request that a time budget or an interrupt stops ends that
process, and the next request starts another.

## The command line

The `sverify` command checks, fixes and runs a pipeline's file from a
shell, a CI job or an agent:

```bash
# skip: runs on pipelines/orders.py, the reader's file
sverify check pipelines/orders.py            # prove every transform and node in the file
sverify check pipelines/orders.py:paid       # one node or transform
sverify check pipelines/orders.py --full     # with each node's full report
sverify check pipelines/orders.py --diff     # the preconditions the proofs need, as a diff
sverify check pipelines/orders.py --fix      # write them into requires=, then check again
sverify check models/orders.sql --schema schemas.yaml   # one SQL query, no Python
sverify refresh pipelines/orders.py:paid     # run a node and report what changed
sverify explain may_be_false                 # what a [code] of check's output means
```

`check` imports the file without running it, so a pull request from a fork is
untrusted code under `pull_request_target`; use `pull_request` for it, or
check out only the base branch. Every contracted transform
the file applies is proved, a node's on its sources' schemas, and a proof
that fails is reported where a call would raise, so one unproved node does
not hide the next. A `refresh()` in the file belongs under
`if __name__ == "__main__":`; while sverify checks the file, it raises. A
directory with a `dbt_project.yml` goes to `sverify-dbt check`.

A `.sql` file holds one query (a second statement is a usage error, exit 2).
`--schema FILE` gives the types of the tables it reads, as YAML or JSON,
`{table: {column: type}}` with the type strings of `sverify.verify(tables=)`.
The verdict is the one `verify` gives with no contract: what the query
computes and what it can raise, with the preconditions it needs. A table the
file does not describe is a usage error, and a construct the lift does not read is
exit 3, by name. `--dialect` and `--semantics` take `sverify.sql`'s values and
defaults (`sverify.sql` documents them). `--fix`, `--diff` and `--against-sink` read
Python files only.

A `DeltaSource` or `IcebergSource` opens its table to learn its schema, which
on a pull request means credentials and a network. Declare it instead,
`DeltaSource(uri, schema=pa.schema([...]))`: `check` proves from the declared
schema and opens nothing, and every refresh compares the table's schema with
the declared one and raises `SchemaError` where they differ, or where a column declared NOT NULL is nullable in the table.

The output starts with the contract in plain words, for a pull request's
comment or a phone's screen: what the output guarantees, what each refresh
checks on the data, and what is not proved, each finding with a code.

```text
Contract of pipelines/orders.py
  The output guarantees:
    paid (p): amount > 10; no two rows share id
  Each refresh checks on the data:
    paid (p): orders: amount ≥ 0; orders: amount < 1000; orders: no two rows share id
  Not proved:
    doubled (d): needs _.amount < 2**62 on orders (else overflow in amount * 2)  [needs]

paid (p): proved
doubled (d): NOT proved: 1 precondition needed
```

`sverify explain <code>` says what a code means and how to fix it, and
`check --full` adds each node's full report, so the default output stays
short in an agent's context. `check --diff` shows the preconditions the
proofs need (`Report.needs`) as a diff of the decorators' `requires=`, and
`check --fix` writes them and checks the file again.

`check --against-sink` compares each stored node's contract with the one
its sink last committed, reading the record and no data. A committed
promise the node no longer proves is a `contract_weakened` finding, and
the check exits 1: a NOT NULL column it no longer proves, a unique key it
widened, or a CHECK whose text is gone and whose proof from the new
contract fails. A tightened bound, a smaller key or a reordered list of
conditions is no drift, and a changed plan or profile is a `plan_changed`
note ([test_drift.py](../python/tests/test_drift.py)). The preconditions a
contract added are not compared: the sink's record does not store them.

`--format` chooses the output:

- `text`, the default, as above;
- `json` (`--json` for short), one document for tools in the format of
  [`cli.schema.json`](../python/src/sverify/schemas/cli.schema.json): the
  exit code and its `status`, for each node its `status`, the plain words
  (`summary`) and its report as `Report.to_json()` writes it, and the
  `findings`, each with its code, level and line;
- for `check`, `github`: GitHub's workflow commands, which annotate the
  transform's line on a pull request in any repository and in the mobile
  app;
- `sarif`: a SARIF 2.1.0 log for code scanning
  (`github/codeql-action/upload-sarif`), one rule per code, with
  `explain`'s text. A transform's first `needs` result carries a fix: the
  edits `check --fix` makes to its `requires=`, as byte ranges of the file.

The codes are snake case (`may_be_false`), as the report's `reason` and
issue `kind` write them; `explain` reads kebab case too. The exit codes are:

| Code | Meaning |
|------|---------|
| 0 | proved, or every postcondition it does not prove is checked on the data at each refresh; a refresh committed every row |
| 1 | not proved |
| 2 | usage error: a flag, a missing file, a node the file lacks |
| 3 | unsupported: a construct outside sverify's model (`sverify.errors.UnsupportedError`) |
| 4 | time or memory budget exceeded |
| 5 | a refresh committed with rows quarantined |
| 6 | error: the file raised, I/O, a crash |
| 7 | refused: no route takes a proved node to the engine |
| 8 | a refresh held a node |

With 5 or 8, `refresh` prints `Refresh.alert()` after the summary, and its
JSON has `"outcome"` and `"alert"` ([bad rows](how-to-quarantine.md#bad-rows-quarantine-and-hold)).
`--examples` adds the rows that broke a condition to both, rows of your
data that otherwise stay out of CI artifacts and issues.

`--timeout` (default 30 s, or `SVERIFY_TIMEOUT`; 0 turns it off) bounds
proof, planning and checking. A refresh moving data has no time limit:
`--memory-limit` (or `SVERIFY_MEMORY_LIMIT`, such as `2GB`) bounds it
instead, as DuckDB's `memory_limit`, past which DuckDB spills to a
temporary directory (`SVERIFY_TEMP_DIRECTORY`), and as Spark's driver
memory. Sverify sets no default of its own: unset, each engine keeps its
own, DuckDB 80 % of the machine's memory
([DuckDB's configuration](https://duckdb.org/docs/stable/configuration/overview)) and
Spark's driver 1 GB ([Spark's configuration](https://spark.apache.org/docs/latest/configuration.html)).
The limit does not reach Polars, which has no memory cap to set; with
`--engine polars` the command says so. A proof has its own cap,
`SVERIFY_CHECKER_MEMORY_MB` (below), since its memory does not grow with
the data. Past any of these budgets the call raises
`sverify.errors.MemoryLimitError` (its `.stage`, `.limit` and `.setting`
say which), a refresh commits nothing, and the command stops with code 4
and reports what was proved before it
([test_memory_limits.py](../python/tests/test_memory_limits.py)).
`sverify.cli.discover(path)` does what `check` does from Python.

## Environment variables

Each variable sets what a flag or a keyword sets; a flag or a keyword
given wins over the variable, and the variable over the default.

| Variable | Flag | Python | Default | Sets |
|---|---|---|---|---|
| `SVERIFY_CHECKER` | | | the bundled checker | the path to a `substrait-check` binary, such as your own `lake build` |
| `SVERIFY_CHECKER_MEMORY_MB` | | | 4096 | the memory, in MB, one checker request may take before the checker is stopped and the request raises `sverify.errors.MemoryLimitError` (Linux and macOS); 0 turns the cap off |
| `SVERIFY_COUNTEREXAMPLES` | | `verify(counterexamples=)` | 200 | how many inputs are tried per unproved postcondition; 0 skips the search |
| `SVERIFY_TIMEOUT` | `--timeout` | | 30 | seconds for proof, planning and checking; 0 turns it off |
| `SVERIFY_MEMORY_LIMIT` | `--memory-limit` | | each engine's own | DuckDB's `memory_limit` and Spark's driver memory, such as `2GB`; not Polars |
| `SVERIFY_TEMP_DIRECTORY` | | | a directory under the system's temporary one | DuckDB's `temp_directory`, where it spills past the memory limit |
| `SVERIFY_STATE_LOCATION` | | | a directory under the system's temporary one | where Polars and Spark write an incremental view's state as Parquet parts: a directory, or a URI (`s3://bucket/state`) that the driver and every executor read and write |
| `SVERIFY_CACHE` | | | on | `off`, `0`, `false` or `no` turns the proof cache off ([Checking without running](#checking-without-running)) |
| `SVERIFY_CACHE_DIR` | | | `$XDG_CACHE_HOME/sverify`, else `~/.cache/sverify` | where the proof cache lives |
| `SVERIFY_SECRETS` | | `Resolver.from_config(path)` | the nearest `pyproject.toml` | the TOML file whose `[tool.sverify.secrets]` table configures named secrets ([Credentials](how-to-credentials.md#credentials)) |
| `SVERIFY_PREBUILT_CHECKER` | | | | for contributors: an editable install links this checker and skips `lake build` |

`SVERIFY_CHECK` and `SVERIFY_SPILL_DIRECTORY`, their names in 0.6, are read
too, with a `DeprecationWarning`.
