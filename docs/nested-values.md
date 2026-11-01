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

## Field and element access (#94)

The rules were decided on #94 from Substrait's spec and the backends (DuckDB,
Polars, Spark, DataFusion):

* **A struct field** is `UnFn.structField i`, Substrait's `StructField`
  reference segment. A struct is the list of its fields, so this is element
  `i` of it. A NULL struct's fields are NULL (DataFusion 51 gives a
  non-NULL value there, see Engines).
* **A list element** is `UnFn.listElement off`, Substrait's `ListElement`
  segment. It is zero-based, a negative offset counts from the end (`-1` is
  the last element), and it is NULL out of range in either direction, without
  wrapping (`Value.listElement`). The offset is a constant, so Ibis's `a[i]`
  needs a literal `i`. SQL's one-based `l[i]` is `i - 1`.
* **`cardinality(l)`** (`functions_list.yaml`) counts NULL elements; a NULL
  list gives NULL, and `[]` gives 0.
* **`contains`** is not a function of its own. Substrait has `any_match(l,
  x -> p)`, which ORs the predicate's results in Kleene logic. The frontend
  chooses the predicate: Ibis's `contains` is `x IS NOT DISTINCT FROM v`
  (NULL matches NULL), and SQL functions keep their engine's meaning (Spark's
  `array_contains` is `x = v`). This needs lambdas in `Expr` (a follow-up).

The parser reads a reference into the input row with nested segments
(`structField` with a `child`), and a reference into an expression's value
(`"expression": …` with a segment). A struct field outside the struct is an
invalid plan, so it is refused. The writer writes both as references into the
value. The abstraction does not look into lists: an element or a field is
`AVal.top`, and a cardinality is a non-negative integer or NULL.

## Engines

Polars runs lists, `collect` (sorting each group's rows when the measure is
ordered) and `UNNEST` (filtering empty and NULL lists before `explode`). The
SQL dialects (DuckDB, Snowflake, Spark) refuse them with `Unsupported` for
now; DuckDB's `ARRAY_AGG … ORDER BY` and `UNNEST` are part of #94.

Polars also runs struct fields, list elements and `cardinality`. The SQL
dialects refuse struct columns and references into values. DataFusion 51
gets no plan with them (`Expr.nestedAccess`): its consumer reads a
reference into an expression's value as a reference into the row, which gives
a wrong column, and its `cardinality([])` is NULL.

## Types in plans

`Parse.Kind` gains `list (k : Kind)` (Substrait's `List` type), so the writer
can type list literals, empty lists and NULLs. `struct (ks : List Kind)` is
Substrait's `Struct` type, positional (its `DecidableEq` is written by hand,
as `Value`'s is). List literals are `{"literal": {"list": {"values": […]}}}`,
an empty list `{"emptyList": {"type": …}}`, a struct literal `{"literal":
{"struct": {"fields": […]}}}`.

A table's `NamedStruct` names its struct columns' fields too, depth first. The
plan's root keeps one name per output column, since sverify reads them as
the columns.

## Follow-ups (#94)

Done: struct field access, list elements and `cardinality` (see above), on
Polars. Still to do:

* lambdas (`Expr` needs `Lambda` and lambda parameter references), and with
  them `any_match` for `contains`, and `transform`/`filter`;
* struct construction;
* lists and structs in the SQL dialects (DuckDB first);
* slicing, and `list.sum`/`min`/`max`/`sort`/`unique`.

Maps and JSON stay out of #94.
