# The layers of the Python package

Sverify's Python modules import each other in one order, from the base up
([#730](https://github.com/AlexanderNenninger/substrait-lean/issues/730)). A
module imports from its own layer and the layers below it, and the imports
inside a layer form no cycle. That holds for imports inside a function too:
one there loads a module late, and never stands in for an import against
the order. Imports under `if TYPE_CHECKING:` serve annotations and may name
any module. [`python/tests/test_layers.py`](../python/tests/test_layers.py)
holds the order (`LAYERS`) and fails on an import against it.

| Layer | Modules | Job |
|---|---|---|
| base | `_meta`, `_deprecated`, `_duration`, `_stages`, `_cursor`, `_unsupported`, `_plan_read`, `_user_text`, `_functions`, `black_box`, `_support`, `plan_json`, `_decimals`, `_polars_shims`, `_duckdb`, `_scan`, `_proof_cache`, `_checker`, `_lean_eval`, `_weighted`, `_hooks`, `_pipe`, `profiles` | The version and the checker protocol, deprecated names, durations, timings, cursors as JSON, errors, the function tables, the plan JSON both frontends write, the reference's decimal types, running `substrait-check`, its cache of proofs and Lean's evaluation of plans, weighted row counts, the hooks, `Pipeable`, engine profiles from outside |
| frontends | `ibis_substrait`, `sql_lift` | Ibis expressions and DuckDB SQL to Substrait plans |
| writers and engines | `sql`, `duckdb_engine`, `polars_engine`, `spark_engine` | The SQL dialects and the engines that run a written plan |
| checker | `engine`, `_engine_settings` | Connections, `plan_json`, `run_plan`, delta plans, the engines' settings |
| conditions | `observation`, `counterexample`, `conditions`, `_quarantine` | The table conditions and their checks on data, what a result is observed up to, the counterexample search, the rows a source sets aside |
| report | `routes`, `report`, `report_json`, `substrait_export`, `_substrait_shims` | What a proof found (`Report`, `Issue`, the errors that carry a report), the routes a plan runs by, the report as JSON and as Substrait |
| transform | `contracts` | `verify`, inferred preconditions, composition and provenance, `transform` |
| incremental | `_state`, `_retention`, `_linear`, `_semi`, `_touched`, `incremental` | Incremental views and their state |
| io | `io` | Delta, Iceberg and Flight sources and sinks |
| nodes | `steps`, `nodes`, `sql_model`, `partition`, `asof` | Pipelines: nodes, steps, SQL steps, partitioned and as-of nodes |
| integrations | `odcs`, `openlineage` | Data contracts (ODCS) and OpenLineage events |
| public | `cli`, `testing`, `pytest_plugin`, `display`, `engines`, `errors`, `sverify` | The public modules and the `sverify` command |

`sverify.contracts` re-exports the names that moved to `conditions` and
`report`, so code that imports them from there keeps working.

## Where a lower layer needs a higher one

A few places hand work up the order, through `sverify._hooks`, which
imports nothing of sverify at load time; the `sverify` command reaches the
core through it too. `import sverify` loads its public names on first use,
so a hook loads its module by name the first time it is called.

- `_hooks.nodes` (`NodeHooks`): a source's `pipe` and a transform called on
  sources build nodes. `sverify.nodes` registers the hooks.
- `_hooks.export` and `_hooks.report_json`: `Report` writes and reads
  itself as Substrait (`to_substrait`, `substrait_contract`, `recheck`) and
  as JSON (`to_json`, `from_json`) through `sverify.substrait_export` and
  `sverify.report_json`.
- `_hooks.lineage`: a refresh with `lineage=` sends its events through
  `sverify.openlineage`.
- `sverify.observation.Tolerant`: the observation's check of a condition
  allows for a tolerance on doubles when the condition is `approx`'s.
  `conditions.Approx` derives from it.

## Readings the frontends share

The Ibis producer, the SQL lift, the SQL writer and the Polars engine read
some constructs the same way. Each such reading has one home
([#731](https://github.com/AlexanderNenninger/substrait-lean/issues/731)).

| Construct | Home | Read by |
|---|---|---|
| Decimal types of `+`, `-`, `×`, `SUM`, `AVG` (`Parse.decimalCall`) | `_decimals` | `ibis_substrait/_base.py`, `sql/core/_base.py`, `polars_engine.py`, `_linear.py`, `report.py` |
| The common type of decimals (`CASE`, `COALESCE`, `IN`) | `_decimals.common` | `ibis_substrait/_base.py`, `sql_lift/_base.py` |
| `BETWEEN`, as `x >= lo AND x <= hi` | `plan_json.between` | `ibis_substrait/core.py`, `ibis_substrait/temporal.py`, `sql_lift/core.py` |
| `IN` lists, and an integer range as `BETWEEN` ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)) | `plan_json.in_values`, `plan_json.int_range` | `ibis_substrait/core.py`, `sql_lift/core.py` |
| `CAST` and `TRY_CAST` | `plan_json.cast_json` | `ibis_substrait/casts.py`, `sql_lift/casts.py` |
| Literals, types, decimal types of values | `plan_json.literal`, `type_json`, `decimal_dtype`, `decimal_type_of` | both frontends |

The SQL lift's arithmetic on decimals follows DuckDB (`sql_lift/core.py`,
and `_digits` in `sql_lift/_base.py`): a product of two decimals of at most
18 digits has at most 18, and its casts round as the engine profile says
([engine-profiles.md](engine-profiles.md)). Those rules are DuckDB's
semantics, and they stay in the lift.
