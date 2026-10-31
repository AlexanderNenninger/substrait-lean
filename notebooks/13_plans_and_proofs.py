# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="13. Plans, meaning and proofs")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 12. [Doubles, time and text](?file=12_values.py) · [Contents](?file=00_start_here.py) · 14. [The checker](?file=14_the_checker.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 13. Plans, meaning and proofs

    The chapters so far were about using the library. If you're the person
    who has to explain to a reviewer why a ✅ can be trusted, this part is
    for you. It starts with the three ideas everything rests on:

    1. a query is a **plan**, a tree of small operators;
    2. a plan has a **meaning**, given by an interpreter that serves as the
       definition of "correct";
    3. a **theorem** is a claim about *all* inputs, and Lean checks its proof.

    Along the way you'll see why SQL's NULL makes "obviously true" claims
    false, and why that is exactly the kind of bug proofs catch and tests
    miss.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## A query is a tree of operators

    When you write

    ```sql
    SELECT id, amount * 2 AS doubled
    FROM orders
    WHERE amount > 10
    ```

    a database does not run the text. It first turns it into a **plan**: a tree
    of small operators, each consuming the rows of its child.
    [Substrait](https://substrait.io) is an open standard for such plans, so
    engines like DataFusion, DuckDB and Polars can exchange them. In this
    project, DataFusion writes the plan and Lean reads it.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.mermaid(
        """
        graph BT
          R["Read orders<br/>(id, customer, amount)"] --> F["Filter<br/>10 &lt; amount"]
          F --> P["Project<br/>append amount * 2"]
          P --> E["Emit<br/>keep columns 0 and 3"]
        """
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Two Substrait quirks worth knowing, because the Lean model copies them:

    * **Columns are numbered, not named.** `amount` is just "column 2"
      (counting from 0). In Lean this is written `$2`.
    * **Project only *adds* columns.** It appends `amount * 2` as column 3; a
      separate **Emit** step then keeps columns 0 and 3. So `SELECT` is
      really "Project, then Emit".

    In Lean, a plan is a value of the type `Rel`, with one case per operator.
    Here is the start of its definition, from `SubstraitLean/Rel.lean`:

    ```lean
    inductive Rel where
      | read (table : String)
      | values (arity : Nat) (rows : Relation)
      | filter (input : Rel) (cond : Expr)
      | project (input : Rel) (exprs : List Expr)
      | emit (input : Rel) (mapping : List Nat)
      | cross (left right : Rel)
      | join (left right : Rel) (type : JoinType) (on : Expr)
      …
    ```

    Read `| filter (input : Rel) (cond : Expr)` as: "a filter is built from
    an input plan and a condition". The recursion (a filter's input is
    itself a plan) is what makes a plan a tree.

    ## A plan has a meaning: the reference interpreter

    To prove anything about plans, we first need to say *precisely* what each
    operator does. In Lean this is a function `Rel.eval` that takes a plan
    and the tables, and returns the result rows. It is written for clarity, not
    speed: it is the **definition** of correct, against which everything else
    is measured.

    Below is a line-for-line Python mirror of the Lean definitions, so you can
    see there is no magic. (The Lean versions are in `SubstraitLean/Expr.lean`
    and `SubstraitLean/Rel.lean`.)
    """)
    return


@app.cell
def _():
    # --- Values: None is SQL NULL -------------------------------------------
    # SQL's three-valued logic: true, false, and "unknown" (NULL).
    def and3(a, b):
        if a is False or b is False:
            return False
        if a is True and b is True:
            return True
        return None

    def eq(a, b):
        return None if a is None or b is None else a == b

    def lt(a, b):
        return None if a is None or b is None else a < b

    def mul(a, b):
        return None if a is None or b is None else a * b

    def is_true(v):
        # WHERE keeps a row only if the condition is *true* (not false, not NULL).
        return v is True

    # --- Operators: a relation is a list of rows, a row is a list of values --
    def filter_rows(rows, cond):
        return [r for r in rows if is_true(cond(r))]

    def project(rows, *exprs):
        return [r + [e(r) for e in exprs] for r in rows]

    def emit(rows, mapping):
        return [[r[i] for i in mapping] for r in rows]

    return and3, emit, eq, filter_rows, is_true, lt, mul, project


@app.cell
def _(emit, filter_rows, lt, mul, project):
    orders = [
        [1, "ada", 30],
        [2, "bob", 5],
        [3, "ada", None],  # amount unknown
    ]

    def query(rows):
        """SELECT id, amount * 2 AS doubled FROM orders WHERE amount > 10"""
        kept = filter_rows(rows, lambda r: lt(10, r[2]))
        with_doubled = project(kept, lambda r: mul(r[2], 2))
        return emit(with_doubled, [0, 3])

    return orders, query


@app.cell(hide_code=True)
def _(display, orders, query):
    display.side_by_side(
        display.table(orders, ["id", "customer", "amount"], title="orders"),
        display.table(query(orders), ["id", "doubled"], title="query(orders)"),
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Notice order 3 disappeared. Its amount is NULL, `10 < NULL` is NULL
    ("unknown"), and a filter only keeps rows whose condition is **true**.
    Keep that in mind; it is the source of most surprises below.

    ## What a theorem looks like

    Optimizers constantly rewrite plans into faster, *supposedly equivalent*
    ones. A classic rewrite merges two filters:

    > `Filter(Filter(r, p), q)` ⟶ `Filter(r, p AND q)`

    Here is how `SubstraitLean/Rewrites.lean` states and proves it:

    ```lean
    theorem filter_filter (r : Rel) (p q : Expr) (cat : Catalog) :
        (filter (filter r p) q).eval cat = (filter r (.bin .and p q)).eval cat := by
      simp [eval, List.filter_filter, Expr.eval, BinFn.apply, isTrue_and3, Bool.and_comm]
    ```

    How to read it:

    | Piece | Meaning |
    |:---|:---|
    | `theorem filter_filter` | the claim's name |
    | `(r : Rel) (p q : Expr) (cat : Catalog)` | **for every** plan `r`, every two conditions `p`, `q`, and every database `cat` |
    | `… .eval cat = … .eval cat` | both plans return exactly the same rows |
    | `:= by simp [...]` | the proof: unfold the definitions and simplify. Lean checks every step mechanically |

    The "for every" is the whole point. A test picks *some* `r`, `p`, `q` and
    some data; the theorem covers **all** of them, including tables with
    millions of rows you will never generate.

    The proof relies on one small fact, `isTrue_and3`: `p AND q` is true
    exactly when both `p` and `q` are true, *even with NULLs*. That fact only
    involves a handful of cases, so we can check every one of them right here,
    which is exactly what Lean's proof does (it splits into cases and checks
    each):
    """)
    return


@app.cell(hide_code=True)
def _(and3, display, is_true):
    _vals = [True, False, None]
    _rows = []
    for _a in _vals:
        for _b in _vals:
            _lhs = is_true(and3(_a, _b))
            _rhs = is_true(_a) and is_true(_b)
            _rows.append([_a, _b, and3(_a, _b), _lhs, _rhs, "✓" if _lhs == _rhs else "✗"])
    display.table(_rows, ["p", "q", "p AND q", "keep? (merged)", "keep? (two filters)", "same"])
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    All nine cases agree, so the merged filter keeps exactly the rows the two
    separate filters keep. Lean checks the same nine cases, and then lifts the
    result to *every* table by reasoning about lists in general.

    ## Why NULL breaks "obvious" rewrites

    Here's a rewrite that looks harmless:

    > `WHERE a = a` ⟶ `WHERE true`  *(every value equals itself, right?)*

    It's **wrong**: `NULL = NULL` is NULL, not true, so the original query
    drops rows where `a` is NULL and the rewritten one keeps them.

    Testing finds this bug only if your test data happens to contain NULLs.
    Try it: generate random test tables and see how often the bug is caught.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    null_rate = mo.ui.slider(
        0, 0.5, step=0.01, value=0.0, label="chance a value is NULL", show_value=True
    )
    n_tests = mo.ui.slider(1, 200, value=20, label="number of random test tables", show_value=True)
    mo.vstack([null_rate, n_tests])
    return n_tests, null_rate


@app.cell(hide_code=True)
def _(eq, filter_rows, mo, n_tests, null_rate):
    import random

    _rng = random.Random(0)
    _caught = 0
    for _ in range(n_tests.value):
        _table = [
            [None if _rng.random() < null_rate.value else _rng.randint(0, 9)] for _ in range(5)
        ]
        _original = filter_rows(_table, lambda r: eq(r[0], r[0]))
        _rewritten = filter_rows(_table, lambda _: True)
        _caught += _original != _rewritten

    mo.callout(
        mo.md(
            f"The bug was caught by **{_caught} of {n_tests.value}** random tests."
            + (
                "  \nWith no NULLs in the data, every test passes, and the bug ships."
                if _caught == 0
                else "  \nOnly tests that happened to contain a NULL could see it."
            )
        ),
        kind="danger" if _caught == 0 else "warn",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Lean can't be fooled this way. To claim the rewrite is correct you would
    have to prove `(a = a)` is true **for every** value of `a`, and the case
    `a = NULL` makes that impossible. The proof attempt fails, which tells you
    the rewrite is unsound before it ever reaches production.

    ## The fine print: hypotheses

    Some rewrites are only correct *under conditions*. For example, a filter
    can be moved below a Project (so fewer rows get the expensive new column),
    **but only if the filter doesn't read the new column**. Lean makes such
    conditions explicit as hypotheses:

    ```lean
    theorem filter_project_pushdown {cat : Catalog} (hcat : cat.WF)
        {r : Rel} {es : List Expr} {p : Expr}
        (hr : r.WF cat) (hp : p.refsLt (r.arity cat)) :
        (filter (project r es) p).eval cat = (project (filter r p) es).eval cat
    ```

    * `hcat`, `hr`: the tables and the input plan are *well-formed*: every
      column reference points at a column that exists (next chapter).
    * `hp`: the condition `p` only references columns that exist *before*
      the projection (`refsLt` = "all column references are less than").

    Hypotheses are not a weakness. They are the precise conditions under which
    the optimization is allowed, written down where a machine can check them.

    Everything the library proves later (contracts, keys, the absence of
    runtime errors, incremental updates) is a theorem of this shape: a
    statement about `Rel.eval` for *every* database, under hypotheses that the
    checker verifies for your particular plan.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.accordion(
        {
            "Try it in Lean": mo.md(r"""
    In `SubstraitLean/Rewrites.lean`, try to prove `filter_project_pushdown`
    **without** the hypothesis `hp`. Lean gets stuck exactly where a filter
    reads a column that only exists after the projection. `lake build` from
    the project root re-checks every proof in a few seconds.
    """),
        }
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 12. [Doubles, time and text](?file=12_values.py) · [Contents](?file=00_start_here.py) · 14. [The checker](?file=14_the_checker.py) →
    """)
    return


if __name__ == "__main__":
    app.run()
