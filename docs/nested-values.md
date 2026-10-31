# Nested values: design

Issue #59 (first step of #94). Lists and structs in the Lean model, `collect`
(Ibis `ArrayCollect`, Polars `implode`) and `unnest` (Ibis `TableUnnest`,
Polars `explode`). Maps, JSON and lambdas are follow-ups (see the end).

## Values

```lean
inductive Value where
  | null | bool (b : Bool) | int (i : Int) | str (s : String)
  | list (vs : List Value)
```

* **One nested constructor.** A list is `.list vs`. A struct is the list of its
  fields, in order: the model is positional everywhere (rows are lists of
  values, columns are ordinals), and the type (`Kind`) in the parser and the
  writer says which one a column holds. A map would be a list of two-field
  structs. Lists of lists nest.
* **Equality** is structural (`DecidableEq`, written by hand: `deriving` does not
  handle the nested inductive). Two lists are equal when they have the same
  length and equal elements, NULL elements equal to NULL. That is what
  DataFusion 51 and DuckDB give for `=`, `GROUP BY` and `DISTINCT` on lists
  (`[1, NULL] = [1, NULL]` is TRUE in both).
* **Order** (`Value.le`, used by `ORDER BY`, windows and `MIN`/`MAX`): lists
  compare lexicographically, a prefix first, NULL elements after every other
  value. Both engines sort `[] < [1] < [1, 2] < [1, NULL] < [NULL]`. NULL moves
  to the end of the type order (booleans < integers < strings < lists < NULL);
  only nested NULLs see it, since sort keys place top-level NULLs by
  `NULLS FIRST/LAST` before comparing values, and `MIN`/`MAX` skip them.
  `Value.le` stays a total order (`Value.le_trans`, `Value.le_total`,
  `Value.le_antisymm`, by mutual recursion over values and lists).
* **Comparison operators** `<`, `<=` on lists are refused: DataFusion says
  `[1, NULL] < [1, 2]` and `[NULL] < [1]` are TRUE, DuckDB FALSE, so they need
  the engine profiles of #23. `MIN`/`MAX` of lists are refused too.

## Abstract values

`AVal` (contracts, runtime errors, keys) does not look inside lists. An
abstract value admits a list exactly where it admits both booleans and a
string (`AVal.top`, or a column's description after `IS NOT NULL`). A
function of integers, booleans or strings gives NULL on a value of another
type, so every existing abstraction already covers a list as it covers a
value of the wrong type, and refinements keep it (`x IS NOT NULL` holds for a
list; `AVal.prune`, which drops empty integer intervals, leaves it). Reusing
the `str` flag alone would be unsound (`length(list)` is NULL, while the
abstraction of `length` on strings says it is not), and so would requiring
the `null` flag (`IS NOT NULL` clears it). Every proof that cases on a
`Value` gains a `.list` case. Length bounds and element descriptions (#59's
"abstract values for lists") are left for when a contract needs them.

`=` on two lists is their structural equality (`BinFn.apply .eq`).

## Collect

`AggFn.collect`: the list of a group's non-NULL values, NULL when there are
none. That is Ibis's `collect()` on DataFusion
(`ARRAY_AGG(x) FILTER (WHERE x IS NOT NULL)`; `ARRAY_AGG` of no rows is NULL
in DataFusion and DuckDB). `include_null=True` and `distinct=True` are
refused for now.

**Order.** A list built from rows is only determined when the aggregate
orders them: Substrait's `AggregateFunction.sorts`, Ibis's
`collect(order_by=…)`. `Measure` gains `sort : List SortKey` (columns of the
input), and the group's rows are sorted stably before they are collected.
Without a sort, `Rel.eval` collects in list order, which is one of the
orders an engine may choose, not the only one. Such a plan still checks;
the abstract value of the result says nothing about its elements, so no
fact about element order is proved, and the differential tests compare
unordered collects as multisets. Reporting the result itself as
undetermined belongs with the other order-dependent results (#55).

The parser accepts `array_agg` only with the filter `x IS NOT NULL` (Ibis's
form), since the model skips NULLs as for every other measure. `collect` is
not decomposable, so it is neither sharded nor maintained incrementally.

## Unnest

No standard Substrait relation exists (`table_functions.md` is unfinished),
so the plan carries it as an `ExtensionSingleRel` with our own detail:

```json
{"extensionSingle": {"input": …, "detail": {
  "@type": "type.googleapis.com/sverify.Unnest", "column": 3, "keepEmpty": false}}}
```

`Rel.unnest (input : Rel) (col : Nat)`: each input row gives one output row
per element of its list in column `col`, with the element in that column's
place (Ibis `t.unnest("xs")` keeps the column where it was); an empty list or
NULL gives no rows. That is `UNNEST` in DataFusion and DuckDB. Polars'
`explode` gives one row of NULL for both, so the Polars engine filters those
rows first. `keep_empty=True` and `offset=` are refused for now.

It is a new `Rel` constructor, so every analysis gets a case:

* arity: the input's; well-formed: `col` in range (and a list, in the parser);
* keys and facts: none (an element can repeat); abstract values: the input's,
  with `col` unknown (`EnvMem.set_top`);
* runtime errors: none of its own. DataFusion pushes filters on the other
  columns below an `UNNEST`, onto rows whose lists may be empty, so
  `Rel.loose` of an unnest is the unnested loose input together with the
  loose input itself;
* guard elimination does not pass through it (`looseSub` is false);
* incremental maintenance and sharding: not yet. It is linear
  (`unnest (a ++ b) = unnest a ++ unnest b`), so `Rel.weighted_eval` and
  `Rel.shardSplit_sound` should extend to it (weights copy to each element's
  row); that is a follow-up.

Ibis's DataFusion compiler has no rule for `TableUnnest`, so the differential
test compares with DuckDB running Ibis's DuckDB SQL.

## Engines

Polars runs lists, `collect` (sorting each group's rows when the measure is
ordered) and `UNNEST` (filtering empty and NULL lists before `explode`). The
SQL dialects (DuckDB, Snowflake, Spark) refuse them with `Unsupported` for
now; DuckDB's `ARRAY_AGG … ORDER BY` and `UNNEST` are part of #94.

## Types in plans

`Parse.Kind` gains `list (k : Kind)` (Substrait's `List` type), so the writer
can type list literals, empty lists and NULLs. Structs (`struct (ks : List
Kind)`) come with #94. List literals are `{"literal": {"list": {"values": […]}}}`,
an empty list `{"emptyList": {"type": …}}`.

## Follow-ups (#94)

Struct construction and field access (`StructField` references), `list.get`,
`list.contains`, `cardinality` (DataFusion: NULL for `[]`, DuckDB: 0, so an
engine-profile question), slicing, `list.sum`/`min`/`max`/`sort`/`unique`,
and `transform`/`filter` with lambdas (`Expr` needs `Lambda` and lambda
parameter references). Maps and JSON stay out of #94.
