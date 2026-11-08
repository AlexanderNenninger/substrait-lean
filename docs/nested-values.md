# Nested values: design

Issue #59 (first step of #94). Lists and structs in the Lean model, `collect`
(Ibis `ArrayCollect`, Polars `implode`) and `unnest` (Ibis `TableUnnest`,
Polars `explode`). Maps and JSON are out of scope ([Follow-ups](#follow-ups)).

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
* **Comparison operators** `<`, `<=` on lists are three-valued, and
  `MIN`/`MAX` of lists order them as `ORDER BY` does
  ([reference-semantics.md](reference-semantics.md#nested-lists-and-structs), #207).
  Engines disagree here: DataFusion says `[1, NULL] < [1, 2]` and
  `[NULL] < [1]` are TRUE, DuckDB FALSE.

## Abstract values

`AVal` (contracts, runtime errors, keys) describes a column by kind (#925):
whether it may be NULL, numbers of a kind (`nk`) within an interval (`int`),
booleans, strings, lists and structs. A list is described by its length
(`card`, an interval) and by one abstract value for all its elements
(`elems`); a struct by one abstract value per field (`fields`). `AVal.Mem`
goes by the value's constructor: `.list vs` is a member when `list` is set,
`vs.length` is in `card` and every element is in `elems`, and `.struct vs`
when `struct` is set and its fields are in `fields`, one each
(`SubstraitLean/Contracts/Lattice.lean`). A function of scalars gives NULL
on a list or a struct, and every scalar abstraction says so through
`nonInt`, `nonBool` and `nonStr`, which include `nested`.

What the checker proves on lists, with the soundness lemma of each step in
`Contracts/TransferSound.lean`, `Contracts/Refine.lean` and
`Contracts/Sound.lean`:

* element bounds and NOT NULL elements: the declared element type
  (`list<i64>` gives elements in the 64-bit range), a lambda's body over an
  element (`transform`, `HoFn.abs_sound`), and a precondition
  `all_match(l, x -> p)` (`Expr.refineL`'s lambda case);
* length bounds: a precondition on `cardinality(l)` (`refineCard`),
  `filter`, which keeps at most the list's length, `transform`, which keeps
  it, and `collect`, at least one value;
* through `UNNEST`, an element in the column's place (`EnvMem.set_elem`); a
  list element, NULL unless the length puts it in range
  (`AVal.elementAbs_sound`); `cardinality`, the length bound
  (`AVal.cardAbs_sound`); a struct field, its field's description
  (`AVal.fieldAbs_sound`); `flatten`, the inner lists' elements.

It does not describe relations between the elements of one list (sorted,
distinct, the first larger than the last), nor anything of a list's
elements past one level of `elems` through `flatten`. The other list
functions (`list_prepend`, `list_concat`, `list_contains`,
`list_position`) and `pair` give `AVal.top`.

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
Without a sort, `Rel.eval` collects in list order, the deterministic
profile's order; the reference allows every order
([D24](core-semantics.md#d24-tie-order-belongs-to-the-deterministic-profile)).
Such a plan still checks, and its postconditions are proved for every
order. The abstract value of the result says nothing about its elements, so
no fact about element order is proved, and the differential tests compare
unordered collects as multisets. The report calls the result not
`deterministic` and names the aggregate in `tie_places`.

Ibis writes `array_agg` with the filter `x IS NOT NULL`, and the model's
measure skips NULLs as every other measure does. DuckDB's `list(x)`, which
keeps NULLs, the SQL lift reads as `flatten(array_agg([x]))`
([reference-semantics.md](reference-semantics.md#nulls-and-order), #810). `collect` is
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
  with `col` an element of its list (`EnvMem.set_elem`, #925);
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
  `array_contains` is `x = v`).

The parser reads a reference into the input row with nested segments
(`structField` with a `child`), and a reference into an expression's value
(`"expression": …` with a segment). A struct field outside the struct is an
invalid plan, so it is refused. The writer writes both as references into the
value. The abstraction reads a list's elements and a struct's fields
([Abstract values](#abstract-values)): an element or a field is described by
its list's or struct's description, and a cardinality by its length.

## Lambdas (#94)

`Expr.hof f l body` is a higher-order function of the list `l`
(`functions_list.yaml`): `any_match` and `all_match` (the predicate's results
ORed and ANDed in Kleene logic, `FALSE` and `TRUE` for `[]`), `transform`
and `filter` (the elements the predicate is `TRUE` for). Each is `NULL` for a
NULL list (`HoFn.apply`).

Lambdas have lexical scope
([D28](core-semantics.md#d28-lambdas-have-lexical-scope)). The body is
evaluated on `x :: row`: it reads its parameter as field 0 and the row's
column `i` as field `i + 1`, and a nested lambda reads its own parameter as
0 and the outer one as 1. The functions that renumber a row's columns
(`mapFields`, `shift`, `subst`, `dropCols`) renumber a body under one binder,
and the analyses read a body over the element in front of the row (over
the list's elements, without facts). Ibis's `contains(v)` still takes
a constant `v`; Polars runs lambdas that read only their parameter
(`pl.element()` sees nothing else), and refuses the others.

* **Errors:** the body runs on every element, so its issues on any element
  are the row's (`Expr.issues`, `Expr.mayIssues_sound`). `verify` reports
  `x -> x * 2` as possibly wrapping around, and Polars raises where it does.
* **Contracts:** `any_match` and `all_match` give a boolean or NULL, TRUE
  only where the body may be (FALSE likewise); `transform` a list of the
  body's values over an element, and `filter` a list of the elements, no
  longer than the list (`HoFn.abs`, #925).
* **Plans:** Substrait's `Lambda` with one parameter. Its body's references
  are `lambdaParameterReference`s (with `steps_out` for an outer lambda's)
  and `rootReference`s; the parser reads them into `x :: row`
  (`Parse.openBody`) and the writer writes them back (`Write.closeRefs`).
* **Kinds:** `Expr.kindT` types a body under the element's kind in front of
  the row's (`Rel.kinds_sound`, `Kinds.lean`).

## Engines

Polars runs lists, `collect` (sorting each group's rows when the measure is
ordered) and `UNNEST` (filtering empty and NULL lists before `explode`).
DuckDB's SQL runs list columns and literals, list elements (`l[i + 1]`, and
`l[i]` for a negative offset), `cardinality` (`len`), `collect` (`list(x
ORDER BY …) FILTER (WHERE x IS NOT NULL)`, the ordinal breaking ties as Lean's
list order does) and `UNNEST` (a lateral `UNNEST(l) WITH ORDINALITY`, so an
order-dependent operation above sees each row's elements in order) (#94).
Snowflake and Spark refuse them until #271.

Polars also runs struct fields, list elements, `cardinality` and the
higher-order functions (the body on `pl.element()` in `list.eval`; a body's
errors are checked over every element). The SQL
dialects refuse struct columns and struct fields. DataFusion 51
gets no plan with them (`Expr.nestedAccess`): its consumer reads a
reference into an expression's value as a reference into the row, which gives
a wrong column, its `cardinality([])` is NULL, and it has no lambdas. The SQL
dialects refuse lambdas too, DuckDB's included for now.

## Types in plans

`Kind` (`Value.lean`) has `list (k : Kind)` (Substrait's `List` type), so the writer
can type list literals, empty lists and NULLs. `struct (ks : List Kind)` is
Substrait's `Struct` type, positional (its `DecidableEq` is written by hand,
as `Value`'s is). List literals are `{"literal": {"list": {"values": […]}}}`,
an empty list `{"emptyList": {"type": …}}`, a struct literal `{"literal":
{"struct": {"fields": […]}}}`.

A table's `NamedStruct` names its struct columns' fields too, depth first. The
plan's root keeps one name per output column, since sverify reads them as
the columns.

## Follow-ups

Struct field access, list elements and `cardinality`, and lambdas with
`any_match`, `all_match`, `transform` and `filter` on Polars, reading the row
and outer parameters in the model (D28), are done (#94). What is still open
is tracked in [#1019](https://github.com/AlexanderNenninger/substrait-lean/issues/1019)
and, for DuckDB's lambdas and list functions,
[#348](https://github.com/AlexanderNenninger/substrait-lean/issues/348); maps
and JSON stay out of #94.
