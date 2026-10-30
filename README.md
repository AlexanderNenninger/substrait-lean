# substrait-lean

**Keep query results up to date without recomputing them, with updates proven correct.**

Say you have a dashboard table built from a join over a few million orders, and
a hundred orders change every hour. Recomputing the whole join each time is
slow. Hand-written incremental logic ("only process rows where `updated_at` is
newer than…") is fast, but it tends to go wrong silently: deletes are missed,
late rows are skipped, a join gets a new match.

This project gives you a third option. You write the query once, in Ibis or SQL,
and `sverify` maintains the result in DuckDB from the inserts and deletes alone.
The update logic comes from a delta plan that is **mathematically proven to give
the same result as a full recompute**. The proof is in [Lean](https://lean-lang.org),
a proof assistant: a program that checks every step of a proof, so you don't
have to take the math on trust.

```python
view = sv.IncrementalView.from_ibis(con, big_orders, "big_orders")
view.apply({"orders": sv.Changes(inserts=[(3, "bob", 50)], deletes=[(1, "ada", 30)])})
# `big_orders` now equals what a full recompute would give, with no recompute.
```

Underneath, queries travel as [Substrait](https://substrait.io), an open,
engine-neutral format for query plans. DuckDB writes your query as a Substrait plan, Lean
checks it and computes the proven update plan, and DuckDB runs that plan.

**New to formal verification?** The [marimo notebook](notebooks/intro.py) is an
interactive introduction with live examples (see [Setup](#setup) for how to open it).

## Setup

You need [uv](https://docs.astral.sh/uv/) for Python and
[elan](https://github.com/leanprover/elan) for Lean (elan is to Lean what
rustup is to Rust, or uv to Python):

```bash
brew install uv          # or: curl -LsSf https://astral.sh/uv/install.sh | sh
```
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Open a new terminal so `lake` (Lean's build tool) is on your PATH. Then, from
the project root:

```bash
lake build                       # checks every proof and builds the substrait-check CLI
```
```bash
cd python && uv sync             # DuckDB 1.2.2, Ibis, pyarrow, pytest, hypothesis
```
```bash
uv run pytest                    # should end with "20 passed"
```

`lake build` has to come first, because the Python package calls the
`substrait-check` binary it produces. The first time you connect, DuckDB
downloads its Substrait extension, so that step needs network access. After
that it is cached in `~/.duckdb`.

To run your own scripts with the package available, from the project root:

```bash
uv run --project python python my_pipeline.py
```

### Development tasks

Tasks are defined with [poe](https://poethepoet.natn.io) in `python/pyproject.toml`:

```bash
cd python && uv run poe qa       # everything below, in order; stops at the first failure
```

| Task | What it does |
|---|---|
| `poe prove` | Checks every Lean proof. Any warning fails, including a `sorry` (an unfinished proof). |
| `poe build` | Builds the `substrait-check` CLI that `sverify` calls |
| `poe lint` | `ruff check` and `ruff format --check` |
| `poe fmt` | Fixes lint issues and formats the Python code |
| `poe typecheck` | Type-checks the Python code with pyrefly |
| `poe golden` | Golden tests: CLI output on every plan in `tests/fixtures` |
| `poe test` | Python tests, including the randomized DuckDB tests |

From the project root, use `uv run --project python poe -C python qa`. The Lean
tasks need `lake` on your PATH.

### The notebook

```bash
uvx marimo run --sandbox notebooks/intro.py      # read-only app view
```
```bash
uv run --project python --with marimo marimo edit notebooks/intro.py   # edit it
```

With the second command, marimo asks whether to run in a sandboxed venv.
Answer **n** to use the project's environment, so cells can `import sverify`.
Answer **Y** to get a sandbox with only the notebook's own dependencies, which
is enough for the introduction.

### Troubleshooting

* **`lake: command not found`**: open a new terminal, or call `~/.elan/bin/lake`.
* **`no configuration file …lakefile`**: run `lake` from the project root, where `lakefile.toml` is.
* **`… does not exist`** for a notebook or `--project` path: those paths are relative to the
  project root, not to `python/`.
* **Why DuckDB 1.2.2?** DuckDB's Substrait extension is only published for 1.2.x,
  not for 1.3 or 2.x.

## Examples

### An incrementally maintained join

```python
import ibis
import sverify as sv

con = sv.connect()  # DuckDB with the Substrait extension loaded
con.sql("create table orders(id bigint, customer varchar, amount bigint)")
con.sql("create table customers(name varchar, city varchar)")
con.sql("insert into orders values (1, 'ada', 30), (2, 'bob', 5)")
con.sql("insert into customers values ('ada', 'Paris')")

db = ibis.duckdb.from_connection(con)
orders, customers = db.table("orders"), db.table("customers")
big_orders = (
    orders.filter(orders.amount > 10)
    .join(customers, orders.customer == customers.name)
    .select(orders.id, customers.city, orders.amount)
)

view = sv.IncrementalView.from_ibis(con, big_orders, "big_orders")
view.rows()                      # [(1, 'Paris', 30)]

# Changes to both tables at once: order 1 leaves, order 3 arrives,
# and bob's new customer row makes his order match the join.
view.apply({
    "orders": sv.Changes(inserts=[(3, "bob", 50)], deletes=[(1, "ada", 30)]),
    "customers": sv.Changes(inserts=[("bob", "Rome")]),
})
view.rows()                      # [(3, 'Rome', 50)]
assert view.rows() == view.recompute()

# An update is a delete plus an insert.
view.apply({"orders": sv.Changes(deletes=[(3, "bob", 50)], inserts=[(3, "bob", 70)])})
view.rows()                      # [(3, 'Rome', 70)]
```

`apply` also updates the base tables, and the whole step runs in one
transaction: if anything fails, for example deleting a row that doesn't exist,
nothing changes. The result is an ordinary DuckDB table, with a `__count`
column for duplicate rows:

```python
con.sql("select * from big_orders").show()
# ┌───────┬─────────┬────────┬─────────┐
# │  id   │  city   │ amount │ __count │
# ├───────┼─────────┼────────┼─────────┤
# │     3 │ Rome    │     70 │       1 │
# └───────┴─────────┴────────┴─────────┘
```

Plain SQL works too: `sv.IncrementalView(con, "select ... from ...", "name")`.
Both routes reach DuckDB as SQL: `from_ibis` compiles the expression with
`ibis.to_sql`. More example pipelines, with unbound tables you can reuse on any
connection, are in [`sverify/examples.py`](python/src/sverify/examples.py).

### What is supported, and what is refused

Supported: filters, computed columns, inner joins (including self-joins), cross
joins and `UNION ALL`. Anything outside that is refused up front instead of
being maintained incorrectly:

```python
sv.IncrementalView.from_ibis(con, orders.limit(5), "top5")
# NotIncremental: not incrementally maintainable (left join or fetch)

totals = orders.group_by("customer").aggregate(total=orders.amount.sum())
sv.IncrementalView.from_ibis(con, totals, "totals")
# ValueError: ... unsupported relation: {"aggregate": ...
```

Aggregates (`GROUP BY` with `SUM`/`COUNT`) are the next thing to add; see
[Possible next steps](#possible-next-steps).

### Pre- and postconditions on a transformation

Declare what you assume about the inputs (`requires`) and what the output
guarantees (`ensures`). Postconditions are **proved** before the expression is
returned, not tested:

```python
from ibis import _
import sverify as sv

@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

expr = doubled(orders)          # proves all three postconditions, then returns the expression
print(doubled.last_report)
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
# ensures id IS NOT NULL: proved
# known about the output:
#   id: any integer
#   doubled: an integer ≥ 22
```

Lean worked out that `doubled` is at least 22: the filter keeps only `amount > 10`,
and doubling preserves that. A postcondition that doesn't follow is refused, along with
the reason:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)

plus_one(orders)
# VerificationError: could not prove: (_.total > 5) (it is TRUE or FALSE)
#   known about the output: total: an integer ≥ 1
```

* **Conditions** can be Ibis expressions (`_.amount >= 0`, or a function of the
  table) or SQL snippets (`"amount >= 0"`). Here's a SQL transformation:
  `sv.verify("select ... from orders where ...", tables={"orders": orders}, ensures=["rest >= 0"])`.
* **Preconditions** are assumptions about data that comes from outside. When the
  inputs are bound to a backend (real tables), they are checked on the data at
  call time and raise `PreconditionError` if violated.
* **Unproved postconditions** raise `VerificationError` by default. With
  `on_unproved="runtime"` they are checked on the output data instead, raising
  `PostconditionError` on a violation. With `on_unproved="warn"` you get a warning.
* **What Lean tracks** per column: whether it can be NULL, an integer range, which
  booleans it can be, and whether it can be a string. Filters like
  `amount > 10`, `amount <= 50`, `x = 3` and `x IS NOT NULL` refine those facts. It
  also understands arithmetic (multiplication by constants), comparisons, `AND`/`OR`/`NOT`
  with SQL NULL semantics, `CASE`, joins and `UNION ALL`. Column schemas count too:
  a non-nullable column (`!int64`) is never NULL.
* **Not tracked yet:** relations between two columns (`a < b`), string contents, and
  facts that only hold across rows (uniqueness, counts).

### Checking a query plan

`substrait-check` reads any Substrait JSON plan, shows it in readable form,
and reports what was verified about it:

```python
plan = sv.substrait_json(con, "select id, amount * 2 as doubled from orders where amount > 10")
open("plan.json", "w").write(plan)
```
```text
$ .lake/build/bin/substrait-check plan.json
Emit [1, 2]                    ← output columns: id, doubled
  Project +[($0 * 2)]          ← append amount * 2
    Filter (10 < $0)           ← amount > 10
      Emit [2, 0]              ← read only (amount, id)
        Read orders
tables: orders(3)
arity: 2
well-formed: yes               ← every column reference exists (a check proven correct)
incremental: yes               ← a proven update plan exists
roundtrip: ok                  ← writing the plan back out reproduces it
rows (0):                      ← named tables carry no data here, only their schema
```

Columns are referred to by position (`$0` is the first column), which is how
Substrait works.

### How do I know it's right?

* **Proofs**: `lake build` re-checks every theorem. The main ones say that the
  update plan computes exactly the change to the result, and that running it on
  DuckDB with the weight-column encoding gives that result. See
  [Proven theorems](#proven-theorems).
* **Randomized testing**: `uv run pytest` generates random tables and random batches of
  inserts and deletes, including NULLs and duplicates. After every batch it
  checks that the maintained result equals a full recompute. This covers the parts
  the proofs don't: the JSON translation, the Python glue and DuckDB itself.
  These tests already caught a real DuckDB bug (see below).

## The formal side

The rest of this README is for people who want to look under the hood.

```bash
lake build                                                  # proofs + CLI
tests/run.sh                                                # golden tests for the CLI
```

There are no dependencies beyond Lean core (no Mathlib yet), so the build takes seconds.

## Checking real plans

`substrait-check plan.json` reads a Substrait plan in protobuf-JSON form, as
produced by DuckDB's `get_substrait_json`, Isthmus or substrait-python. It then:

1. translates it into the formal `Rel` model, or rejects anything outside the fragment (exit 1);
2. decides `Rel.WF` with `checkWF`, which is proven equivalent (`checkWF_iff`), and
   checks that `RelRoot.names` match the output arity (exit 2 if ill-formed);
3. evaluates the plan. Named tables are schema-only (arity from `baseSchema`, no rows),
   so only `VirtualTable` data produces output rows.

```text
$ substrait-check tests/fixtures/virtual_left_join.json
Emit [0, 4]
  Project +[IF IS_NULL($3) THEN "unknown" ELSE $3]
    LeftJoin ($1 = $3)
      Values[3] 3 row(s)
      Values[1] 2 row(s)
arity: 2
well-formed: yes
rows (3):
  (1, "ada")
  (2, "unknown")
  (3, "ada")
```

Supported: `read` (named / virtual table, `filter`, `projection` mask), `filter`, `project`, `cross`,
`join` (inner, left), `fetch` (literal offset/count), `set` (union all), and
`RelCommon.emit`. Expressions: literals (bool, integers, string, null), direct
field references, `ifThen`, casts of integer literals to integer types, and scalar functions `and`, `or`, `not`, `is_null`,
`is_not_null`, `negate`, `add`, `subtract`, `multiply`, `equal`, `not_equal`,
`lt`, `gt`, `lte`, `gte`, matched by name in `extensions`.

The CLI also reports whether the plan is in the incremental fragment
(`isIncremental`, proven equivalent to `Rel.Incremental`) and whether writing
it back out as JSON and re-parsing gives the same `Rel` (`roundtrip: ok`).

The parser ([Parse.lean](SubstraitLean/Parse.lean)) and writer
([Write.lean](SubstraitLean/Write.lean)) are **trusted, unverified code**. The
proofs are about `Rel`, so a parser bug would make the CLI check the wrong plan.
The golden tests in `tests/fixtures` are the guard against that. The
`duckdb_*.json` fixtures are real plans: the Ibis pipelines in
`sverify/examples.py`, compiled by Ibis and DuckDB
(`python/scripts/capture_fixtures.py`). The others are hand-written.

## Incremental views in Python

`python/` holds `sverify`, which maintains DuckDB query results incrementally
using delta plans from Lean:

```python
import sverify as sv

con = sv.connect()          # DuckDB with the substrait extension loaded
...                         # create and fill `orders`, `customers`
from sverify.examples import PIPELINES

view = sv.IncrementalView.from_ibis(con, PIPELINES["inner_join"], "v")
view.apply({"orders": sv.Changes(inserts=[(3, "bob", 7)], deletes=[(1, "ada", 30)]),
            "customers": sv.Changes(inserts=[("bob", "Rome")])})
assert view.rows() == view.recompute()
```

`IncrementalView(con, sql, name)` takes a SQL string instead. Both go through
DuckDB's own Substrait producer; for Ibis, `ibis.to_sql` writes the SQL.

How it works:

1. DuckDB compiles the SQL to Substrait, with the optimizer disabled (with it
   on, DuckDB uses table statistics and drops a `WHERE` on an empty table, so
   the plan would only be valid for the data at capture time).
2. `substrait-check --delta` compiles the plan with `Rel.delta`, splits it into
   union-free terms (`Rel.terms`) and applies the weight-column encoding
   (`Rel.weighted`). It prints one Substrait plan per term, after checking each
   one is incremental and well-formed.
3. For each change batch, `sverify` loads the change tables `t$delta` (rows plus
   `__weight` = ±1), runs every term with `from_substrait_json`, concatenates the
   outputs, consolidates them (`GROUP BY … SUM(__weight)`), and merges the
   result into the stored view (rows plus a `__count` multiplicity).

`python/tests/test_incremental.py` is a differential test (with `hypothesis`):
after random insert/delete batches, the maintained view must equal the query
recomputed from scratch. It runs every pipeline in `sverify/examples.py`:
filters and projections, inner joins, self-joins, `UNION ALL`, cross products,
and a filter-join-compute chain. It also runs one plain-SQL query, so the SQL
entry point stays covered.

**Engine findings.** The substrait extension is only published for DuckDB
1.2.x, so `duckdb==1.2.2` is pinned. Its consumer also runs `SET_OP_UNION_ALL` as
`UNION DISTINCT`, which loses duplicate rows. The differential test caught this,
and it's the reason delta plans are split into union-free terms.

**Trusted components** (not covered by the proofs): the JSON parser and
writer, the `sverify` glue (change tables, consolidation, merge), and DuckDB's
execution of Substrait. These are covered by golden tests, round trips and the
differential test instead.

## What's here

| File | Contents |
|---|---|
| `SubstraitLean/Value.lean` | Nullable values, rows, bag-semantics relations |
| `SubstraitLean/Expr.lean` | `Literal`, `FieldReference`, scalar functions, `IfThen`, Kleene 3-valued logic |
| `SubstraitLean/Rel.lean` | `Read`, `VirtualTable`, `Filter`, `Project`, `Emit`, `Cross`, `Join` (inner/left), `Fetch`, `UnionAll`; arity, well-formedness, `eval`; **type soundness** |
| `SubstraitLean/Rewrites.lean` | Verified rewrites (below) |
| `SubstraitLean/Incremental.lean` | Z-set semantics, delta rules, delta plans (incremental view maintenance) |
| `SubstraitLean/Terms.lean` | Splitting a plan into union-free terms |
| `SubstraitLean/Weighted.lean` | Weight-column encoding for bag engines; `isIncremental` |
| `SubstraitLean/Write.lean` | `Rel` → Substrait JSON, delta plans for engines (trusted) |
| `SubstraitLean/Contracts.lean` | Verified abstract interpreter: NULLs, intervals, filter refinement; `contract_sound` |
| `SubstraitLean/ContractCheck.lean` | `--contract`: proving postconditions from preconditions and schemas |
| `SubstraitLean/Check.lean` | Executable `checkWF`, proven equivalent to `Rel.WF`; `Decidable` instance |
| `SubstraitLean/Parse.lean` | Substrait protobuf-JSON → `Rel` (trusted) |
| `SubstraitLean/Pretty.lean` | Plan / row rendering |
| `Main.lean` | `substrait-check` CLI (`--delta` for engine delta plans) |
| `python/` | `sverify`: incremental views on DuckDB, differential tests |
| `SubstraitLean/Examples.lean` | Concrete plans checked with `#guard` at build time, plus `#print axioms` |

### Proven theorems

* `Rel.eval_arity`: a well-formed plan on a well-formed catalog only produces
  rows of its declared arity.
* `filter_filter`: `Filter(Filter(r,p),q) = Filter(r, p AND q)`, which also holds under three-valued logic.
* `filter_true`, `fetch_zero_none`: identity eliminations.
* `filter_unionAll`: filter distributes over `UNION ALL`.
* `unionAll_comm`: `UNION ALL` commutes up to bag equivalence (`≈ᵣ`).
* `join_inner_eq_filter_cross`: an inner join is a filtered cross product.
* `filter_project_pushdown`: a filter that only reads input columns can be moved below a `ProjectRel`.
* `filter_cross_pushdown_left`: a filter that only reads left columns can be pushed into the left side of a `CrossRel`.
* `emit_project_identity`: emitting only the input columns of a `ProjectRel` removes the projection.

### Contracts

[Contracts.lean](SubstraitLean/Contracts.lean) is an abstract interpreter
over `Rel`. Each column gets an `AVal`, a set of possible values: whether it can be NULL, an integer
interval, possible booleans, and whether it can be a string.

* `Expr.abs_sound`: abstract evaluation of expressions is sound, including SQL's
  three-valued `AND`/`OR`, NULL-propagating arithmetic and comparisons.
* `Expr.refine_sound`: a row that passes a filter satisfies what the condition
  says about its columns.
* `Rel.aeval_sound`: every row a well-formed plan produces is described by `Rel.aeval`.
* `Rel.colExprs_eval`: a precondition plan (`orders.select(cond, ...)`) computes its
  conditions row by row, so "all its columns are TRUE" is the precondition.
* `contract_sound`: suppose every input row matches its schema and satisfies its
  preconditions. If every column of the postcondition plan is certainly TRUE,
  then every output row satisfies every postcondition.

Trusted: the schema description taken from `baseSchema` types and nullability, and
the JSON plumbing.

### Incremental view maintenance

Table updates are Z-sets: rows with signed weights, where a deletion has weight `-1` and an
update is a delete plus an insert. This follows DBSP (Budiu et al., VLDB 2023).
It covers every operator except left join and fetch (`Rel.Incremental`):

* `Rel.zeval_add`: `Q(D + ΔD) ~ Q(D) + ΔQ`. Filter, project, emit and union are
  linear, and cross and inner join use the bilinear rule
  `Δ(A×B) = ΔA×(B+ΔB) + A×ΔB`.
* `Rel.delta`: compiles a plan into a **delta plan**, an ordinary `Rel` that reads the
  old tables and the change tables (`δ t`, e.g. `orders$delta`).
  `Rel.delta_correct` proves it computes exactly `ΔQ`.
* `Rel.incremental_sound`: combines the two, so old result + delta-plan output =
  full recomputation.
* `Rel.zeval_lift`: with all weights 1, Z-set evaluation equals the bag
  semantics `Rel.eval`, so the two models agree.
* `Rel.zeval_terms`: a plan's result is the concatenation of its union-free
  terms' results (`Rel.terms`).
* `Rel.weighted_eval`: running the weight-column encoding (`Rel.weighted`) on an
  ordinary bag engine gives exactly the Z-set result, with each weight as a
  trailing column. Old tables get weight 1, and joins multiply weights.

Equivalence is `List.Perm`, which never cancels `+1` against `-1`. That makes it
stronger than Z-set equality, so the results also hold under consolidation.
`Examples.lean` runs a delete, an insert and an update through a filter/project
plan and an inner join where both sides change.

All proofs depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Modelling choices

* **Positional schemas.** Substrait field references are ordinals, so a
  schema is just an arity. Types beyond "nullable value" are not tracked yet.
* **Project appends, Emit narrows.** This matches Substrait's `ProjectRel` +
  `RelCommon.emit`. Here `Emit` is its own node rather than a field on every rel.
* **Bags as lists.** `Rel.eval` returns a `List`, and plan equivalence is `List.Perm`.
  Several rewrites are stronger than that and hold as exact list equality.
* **Fetch is order-dependent.** Without a `SortRel`, real engines may return any
  rows. The semantics fixes list order, so `fetch` theorems describe one valid behavior.
* **Ill-typed calls evaluate to `null`.** This keeps `eval` total. `Rel.WF` rules out
  out-of-range field references.

## Prior work to build on

No existing formal semantics for Substrait came up in my search. The closest work formalizes SQL or relational algebra:

**Coq (most mature)**
* **SQLCert / SQL_Coq** (Benzaken, Contejean): a mechanized semantics for
  realistic SQL with nulls, aggregates and correlated subqueries, an extended bag
  algebra, and proofs of common optimizer rewrites.
  [HAL 01487062](https://hal.archives-ouvertes.fr/hal-01487062),
  [HAL 01955433](https://hal.archives-ouvertes.fr/hal-01955433)
* **HoTTSQL** (Chu, Weitz, Cheung, Suciu; PLDI 2017): denotes queries as
  K-relations using univalence. It proves many rewrite rules, and the Cosette prover grew out of it.
  [arXiv 1607.04822](https://arxiv.org/abs/1607.04822),
  [PLDI page](https://pldi17.sigplan.org/event/pldi-2017-papers-hottsql-proving-query-rewrites-with-univalent-sql-semantics)
* **A Formalization of SQL with Nulls** (Ricciotti, Cheney; JAR 2022): covers
  three-valued logic, set and bag operations, lateral joins and nested subqueries.
  [arXiv 2003.11331](https://arxiv.org/abs/2003.11331),
  [PMC9637088](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC9637088/)
* **Q\*cert** (Auerbach et al., SIGMOD 2017): a verified query compiler
  built around the nested relational algebra (NRA<sup>e</sup>). It's the closest
  analogue to "verified IR for queries".

**Lean 4**
* **RelationalAlgebra** (Rickerd): relational algebra ≡ first-order logic, built on Mathlib.
  [Reservoir](https://reservoir.lean-lang.org/@Rickerd1234/RelationalAlgebra)
* **provenance** (Senellart): semantics for ProvSQL with semiring provenance,
  a natural route to K-relation semantics in Lean.
  [Reservoir](https://reservoir.lean-lang.org/@PierreSenellart/provenance)
* Emergence AI's [Lean SQL equivalence write-up](https://www.emergence.ai/blog/formal-verification-of-sql-queries-in-lean-for-enhanced-accuracy)
  and the typed-queries chapter of
  [*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Worked-Example___-Typed-Queries/).

## Possible next steps

0. **Non-linear operators.** Aggregates (SUM/COUNT per group are linear over
   Z-sets), DISTINCT and left join. DuckDB's real plans use `AggregateRel` a lot.
1. **More producers.** Capture plans from Isthmus or DataFusion, and consider
   DataFusion as a second consumer, since DuckDB's Substrait support is stuck on 1.2.
2. **Translation validation.** Given a plan and its optimized form, have Lean
   check that they are equivalent. A decision procedure for the conjunctive
   fragment would mirror Cosette and HoTTSQL.
3. **AggregateRel and SortRel.** Grouping semantics would follow Benzaken and
   Contejean. A sort would make `fetch` deterministic.
4. **Real types.** Add a typing judgement over Substrait types (i32/i64 overflow,
   decimals, nullability) and prove `eval` respects it.
5. **Mathlib `Multiset` or K-relations.** Move bag equivalence to quotients, or
   generalize to semiring-annotated relations as HoTTSQL and provenance do.
6. **Compare the Lean evaluator with engines.** The current differential test
   compares incremental and full evaluation, both on DuckDB. Comparing Lean's
   `eval` with DuckDB on generated data would check the semantics itself.
