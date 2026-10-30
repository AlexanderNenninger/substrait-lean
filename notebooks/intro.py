# /// script
# requires-python = ">=3.12"
# dependencies = ["marimo"]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="Verified data pipelines")


@app.cell(hide_code=True)
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Verified data pipelines: a gentle introduction

    You already know what a data pipeline is: read some tables, filter, compute
    new columns, join, union, and hope the result is right. This notebook
    explains what it means to **prove** that a pipeline (or a change to one) is
    right, using the Lean project in this repository.

    No prior knowledge of formal verification is assumed. Every idea comes
    with a small example you can play with.

    **The roadmap**

    1. A query is a *plan*: a tree of operators (Substrait).
    2. A plan has a *meaning*: an interpreter we agree to treat as the definition.
    3. A *theorem* is a claim about **all** inputs, not just the ones in your tests.
    4. Why NULL makes "obviously true" rewrites false.
    5. Well-formedness: the column-count bugs a checker can rule out.
    6. Incremental updates: refreshing a result from just the changed rows, provably.
    7. What is proven, and what is still trusted.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.callout(
        mo.md(
            "**Tests vs. proofs, in one sentence.** A test checks that your "
            "pipeline is right *on the data you tried*. A proof checks that it is "
            "right *on every possible dataset*, including ones with NULLs, "
            "duplicates, empty tables and values you never thought of."
        ),
        kind="info",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. A query is a tree of operators

    When you write

    ```sql
    SELECT id, amount * 2 AS doubled
    FROM orders
    WHERE amount > 10
    ```

    a database does not run the text. It first turns it into a **plan**: a tree
    of small operators, each consuming the rows of its child.
    [Substrait](https://substrait.io) is a standard format for such plans, so
    DuckDB, DataFusion, Arrow and others can exchange them.

    Here is the plan for the query above, as Substrait actually writes it:
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

    * **Columns are numbered, not named.** `amount` is just "column 2" (counting from 0).
      In Lean this is written `$2`.
    * **Project only *adds* columns.** It appends `amount * 2` as column 3; a
      separate **Emit** step then keeps columns 0 and 3. So `SELECT` is
      really "Project, then Emit".
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. A plan has a meaning: the reference interpreter

    To prove anything about plans, we first need to say *precisely* what each
    operator does. In Lean this is a function `Rel.eval` that takes a plan
    and the tables, and returns the result rows. It is written for clarity, not
    speed: it is the **definition** of correct, against which everything else
    is measured.

    Below is a line-for-line Python mirror of the Lean definitions, so you can
    see there is no magic. (The Lean versions are in
    `SubstraitLean/Expr.lean` and `SubstraitLean/Rel.lean`.)
    """)
    return


@app.cell
def _():
    # --- Values: None is SQL NULL -------------------------------------------
    def show(v):
        if v is None:
            return "NULL"
        if v is True:
            return "true"
        if v is False:
            return "false"
        return repr(v)

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

    def cross(a, b):
        return [x + y for x in a for y in b]

    return and3, cross, emit, eq, filter_rows, is_true, lt, mul, project, show


@app.cell
def _(emit, filter_rows, lt, mul, project):
    orders = [
        [1, "ada", 30],
        [2, "bob", 5],
        [3, "ada", None],  # amount unknown
    ]

    def query(rows):
        """SELECT id, amount * 2 FROM orders WHERE amount > 10"""
        kept = filter_rows(rows, lambda r: lt(10, r[2]))
        with_doubled = project(kept, lambda r: mul(r[2], 2))
        return emit(with_doubled, [0, 3])

    return orders, query


@app.cell(hide_code=True)
def _(mo, orders, query, show):
    def as_table(rows, columns, weights=None):
        """A small static table; weights are shown in green (+) or red (−)."""
        cols = list(columns) + (["weight"] if weights is not None else [])
        cell = "text-align:left;padding:4px 16px 4px 0"
        head = "".join(f"<th style='{cell}'>{c}</th>" for c in cols)
        body = []
        for i, r in enumerate(rows):
            cells = "".join(
                f"<td style='{cell};opacity:.5'>NULL</td>"
                if v is None
                else f"<td style='{cell}'>{v if isinstance(v, str) else show(v)}</td>"
                for v in r
            )
            if weights is not None:
                w = weights[i]
                color = "#2e8b57" if w > 0 else "#c0392b"
                cells += f"<td style='{cell};color:{color};font-weight:600'>{'+' if w > 0 else '−'}{abs(w)}</td>"
            body.append(f"<tr>{cells}</tr>")
        if not rows:
            body.append(f"<tr><td colspan='{len(cols)}' style='opacity:.55'><em>(empty)</em></td></tr>")
        return mo.Html(
            "<table style='border-collapse:collapse;font-size:0.9rem;width:auto;margin:0'>"
            f"<thead><tr>{head}</tr></thead><tbody>{''.join(body)}</tbody></table>"
        )

    mo.hstack(
        [
            mo.vstack([mo.md("**orders**"), as_table(orders, ["id", "customer", "amount"])]),
            mo.vstack([mo.md("**query(orders)**"), as_table(query(orders), ["id", "doubled"])]),
        ],
        justify="start",
        gap=2,
    )
    return (as_table,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Notice order 3 disappeared. Its amount is NULL, `10 < NULL` is NULL
    ("unknown"), and a filter only keeps rows whose condition is **true**.
    Keep that in mind; it is the source of most surprises below.

    ## 3. What a theorem looks like

    Optimizers constantly rewrite plans into faster, *supposedly equivalent*
    ones. A classic rewrite merges two filters:

    > `Filter(Filter(r, p), q)` ⟶ `Filter(r, p AND q)`

    Here is how the Lean file `SubstraitLean/Rewrites.lean` states and proves it:

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
    which is exactly what Lean's proof does (it splits into cases and checks each):
    """)
    return


@app.cell(hide_code=True)
def _(and3, as_table, is_true):
    _vals = [True, False, None]
    _rows, _ok = [], True
    for _a in _vals:
        for _b in _vals:
            _lhs = is_true(and3(_a, _b))
            _rhs = is_true(_a) and is_true(_b)
            _ok &= _lhs == _rhs
            _rows.append([_a, _b, and3(_a, _b), _lhs, _rhs, "✓" if _lhs == _rhs else "✗"])
    as_table(_rows, ["p", "q", "p AND q", "keep? (merged)", "keep? (two filters)", "same"])
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    All nine cases agree, so the merged filter keeps exactly the rows the two
    separate filters keep. Lean checks the same nine cases, and then lifts the
    result to *every* table by reasoning about lists in general.

    ## 4. Why NULL breaks "obvious" rewrites

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
    null_rate = mo.ui.slider(0, 0.5, step=0.01, value=0.0, label="chance a value is NULL", show_value=True)
    n_tests = mo.ui.slider(1, 200, value=20, label="number of random test tables", show_value=True)
    mo.vstack([null_rate, n_tests])
    return n_tests, null_rate


@app.cell(hide_code=True)
def _(eq, filter_rows, mo, n_tests, null_rate):
    import random

    _rng = random.Random(0)
    _caught = 0
    for _ in range(n_tests.value):
        _table = [[None if _rng.random() < null_rate.value else _rng.randint(0, 9)] for _ in range(5)]
        _original = filter_rows(_table, lambda r: eq(r[0], r[0]))
        _rewritten = filter_rows(_table, lambda r: True)
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

    ### The fine print: hypotheses

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

    * `hcat`, `hr`: the tables and the input plan are well-formed (next section).
    * `hp`: the condition `p` only references columns that exist *before*
      the projection (`refsLt` = "all column references are less than").

    Hypotheses are not a weakness. They are the precise conditions under which
    the optimization is allowed, written down where a machine can check them.

    ## 5. Well-formedness: ruling out column bugs

    Since columns are numbered, a common bug is a reference to a column that
    doesn't exist: `$5` on a table with 3 columns. The Lean project has a
    checker for this, and a proof (`checkWF_iff`) that the checker answers
    exactly the mathematical definition `Rel.WF`.

    The command-line tool `substrait-check` parses a real Substrait JSON plan,
    runs that checker, and evaluates the plan. Move the slider to change which
    column the filter in our query reads:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    import json
    import pathlib
    import subprocess
    import tempfile

    _here = mo.notebook_dir() or pathlib.Path(__file__).parent
    ROOT = pathlib.Path(_here).resolve().parent
    CLI = ROOT / ".lake" / "build" / "bin" / "substrait-check"
    BASE_PLAN = json.loads((ROOT / "tests" / "fixtures" / "filter_project.json").read_text())

    def run_check(plan):
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
            json.dump(plan, f)
        proc = subprocess.run([str(CLI), f.name], capture_output=True, text=True)
        return proc.returncode, (proc.stdout + proc.stderr).strip()

    field_index = mo.ui.slider(0, 5, value=2, label="filter reads column $", show_value=True)
    field_index
    return BASE_PLAN, CLI, field_index, json, run_check


@app.cell(hide_code=True)
def _(BASE_PLAN, CLI, field_index, json, mo, run_check):
    if not CLI.exists():
        _out = mo.callout(
            mo.md("Build the checker first: run `lake build` in the project root, then re-run this cell."),
            kind="warn",
        )
    else:
        _plan = json.loads(json.dumps(BASE_PLAN))
        _cond = _plan["relations"][0]["root"]["input"]["project"]["input"]["filter"]["condition"]
        _cond["scalarFunction"]["arguments"][0]["value"]["selection"]["directReference"]["structField"][
            "field"
        ] = field_index.value
        _code, _text = run_check(_plan)
        # `orders` is schema-only here (no data), so the row listing is always empty.
        _text = "\n".join(l for l in _text.splitlines() if not l.startswith("rows"))
        _verdict = {
            0: ("success", "Well-formed: every column reference exists."),
            2: ("danger", f"Rejected: `orders` has 3 columns (0–2), so `${field_index.value}` doesn't exist."),
        }.get(_code, ("warn", "The plan could not be parsed."))
        _out = mo.vstack(
            [
                mo.md(f"```text\n$ substrait-check filter_project.json\n{_text}\n```"),
                mo.callout(mo.md(_verdict[1]), kind=_verdict[0]),
            ]
        )
    _out
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Why does a proof about this checker matter? Because the main
    type-safety theorem, `Rel.eval_arity`, says:

    > If a plan is well-formed, **every** row it outputs has exactly the
    > number of columns the plan declares.

    So when the checker says yes, the theorem applies, and so do the rewrites
    that need well-formedness as a hypothesis.

    ## 6. Incremental updates: refresh from just the changes

    Recomputing a big result every time a few rows change is wasteful.
    *Incremental view maintenance* computes only the **change** to the result
    from the **change** to the inputs. It's also easy to get subtly wrong.

    The trick that makes it tractable is to give every row a **weight**:

    * `+1`: this row was inserted,
    * `−1`: this row was deleted,
    * an update is a delete plus an insert.

    A table with weights is called a *Z-set*. Adding a batch of changes is just
    putting the weighted rows together and summing weights per row.

    Pick some changes to `orders`:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    changes = [
        mo.ui.checkbox(value=True, label="Delete order 1 (ada, 30)"),
        mo.ui.checkbox(value=True, label="Insert order 4 (cy, 50)"),
        mo.ui.checkbox(value=True, label="Update order 2: amount 5 → 20"),
        mo.ui.checkbox(value=False, label="Insert order 5 (dee, amount NULL)"),
    ]
    mo.vstack(changes, gap=0.25)
    return (changes,)


@app.cell
def _(is_true, lt, mul):
    # Z-sets: lists of (row, weight). These mirror SubstraitLean/Incremental.lean.
    def z_lift(rows):
        return [(r, 1) for r in rows]

    def z_filter(z, cond):
        return [(r, w) for r, w in z if is_true(cond(r))]

    def z_map(z, f):
        return [(f(r), w) for r, w in z]

    def z_cross(a, b):
        return [(x + y, w * v) for x, w in a for y, v in b]

    def consolidate(z):
        """Sum the weights of equal rows; drop rows whose weight is 0."""
        totals = {}
        for r, w in z:
            totals[tuple(r)] = totals.get(tuple(r), 0) + w
        return sorted(((list(r), w) for r, w in totals.items() if w != 0), key=repr)

    def z_query(z):
        """The same query as before, on weighted rows."""
        kept = z_filter(z, lambda r: lt(10, r[2]))
        return z_map(kept, lambda r: [r[0], mul(r[2], 2)])

    return consolidate, z_cross, z_filter, z_lift, z_query


@app.cell(hide_code=True)
def _(changes):
    _all_changes = [
        [([1, "ada", 30], -1)],
        [([4, "cy", 50], +1)],
        [([2, "bob", 5], -1), ([2, "bob", 20], +1)],
        [([5, "dee", None], +1)],
    ]
    delta_orders = [c for box, cs in zip(changes, _all_changes) if box.value for c in cs]
    return (delta_orders,)


@app.cell(hide_code=True)
def _(as_table, consolidate, delta_orders, mo, orders, z_lift, z_query):
    _old = consolidate(z_query(z_lift(orders)))
    _delta_out = consolidate(z_query(delta_orders))
    _incremental = consolidate(z_query(z_lift(orders)) + z_query(delta_orders))
    _recomputed = consolidate(z_query(z_lift(orders) + delta_orders))

    def _zt(z, cols):
        return as_table([r for r, _ in z], cols, [w for _, w in z])

    mo.vstack(
        [
            mo.hstack(
                [
                    mo.vstack([mo.md("**Δ orders** (the changes)"), _zt(delta_orders, ["id", "customer", "amount"])]),
                    mo.vstack([mo.md("**query(Δ orders)**: the change to the result"), _zt(_delta_out, ["id", "doubled"])]),
                ],
                justify="start",
                gap=2,
            ),
            mo.hstack(
                [
                    mo.vstack([mo.md("**old result**"), _zt(_old, ["id", "doubled"])]),
                    mo.vstack([mo.md("**old + change** (incremental)"), _zt(_incremental, ["id", "doubled"])]),
                    mo.vstack([mo.md("**recomputed from scratch**"), _zt(_recomputed, ["id", "doubled"])]),
                ],
                justify="start",
                gap=2,
            ),
            mo.callout(
                mo.md(
                    "Incremental result **equals** full recomputation ✓"
                    if _incremental == _recomputed
                    else "Mismatch ✗"
                ),
                kind="success" if _incremental == _recomputed else "danger",
            ),
        ],
        gap=1.5,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    For this query the rule is simple: **run the same query on just the
    changes**, then add the result to the old one. That works because filter
    and project treat each row independently (they are *linear*).

    In Lean that is theorem `Rel.zeval_add`:

    ```lean
    theorem Rel.zeval_add : r.Incremental →
        (r.zeval (cat + Δ)).Perm (r.zeval cat ++ r.zdelta cat Δ)
    ```

    Read: *for every plan in the supported fragment, evaluating on the updated
    database gives the old result plus the delta (in some order: `Perm` means
    "same rows, possibly reordered").*

    ### Joins are trickier

    A join pairs rows from two tables. If **both** tables change, the new
    result has four kinds of pairs:

    | | old customers `B` | new customers `ΔB` |
    |:---|:---|:---|
    | **old orders `A`** | `A × B`: already in the old result | `A × ΔB`: new |
    | **new orders `ΔA`** | `ΔA × B`: new | `ΔA × ΔB`: new, and easy to forget! |

    So the change to a join is `ΔA × (B + ΔB) + A × ΔB`. Forgetting the
    bottom-right cell is a classic bug in hand-written incremental pipelines.
    Toggle it off to see what goes wrong:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    include_corner = mo.ui.switch(value=True, label="include the ΔA × ΔB term")
    include_corner
    return (include_corner,)


@app.cell(hide_code=True)
def _(
    as_table,
    consolidate,
    delta_orders,
    eq,
    include_corner,
    mo,
    orders,
    z_cross,
    z_filter,
    z_lift,
):
    _customers = z_lift([["ada", "Paris"], ["bob", "Oslo"]])
    _delta_customers = [(["cy", "Lima"], +1), (["bob", "Oslo"], -1)]

    def _join(a, b):
        # orders.customer ($1) = customers.name ($3)
        return z_filter(z_cross(a, b), lambda r: eq(r[1], r[3]))

    _A, _dA = z_lift(orders), delta_orders
    _B, _dB = _customers, _delta_customers
    _delta = _join(_dA, _B) + _join(_A, _dB) + (_join(_dA, _dB) if include_corner.value else [])
    _incremental = consolidate(_join(_A, _B) + _delta)
    _recomputed = consolidate(_join(_A + _dA, _B + _dB))
    _cols = ["id", "customer", "amount", "name", "city"]

    def _zt(z):
        return as_table([r for r, _ in z], _cols, [w for _, w in z])

    mo.vstack(
        [
            mo.md("Customer changes: insert **cy (Lima)**, delete **bob (Oslo)**. Order changes: as selected above."),
            mo.hstack(
                [
                    mo.vstack([mo.md("**incremental** (old join + delta)"), _zt(_incremental)]),
                    mo.vstack([mo.md("**recomputed from scratch**"), _zt(_recomputed)]),
                ],
                justify="start",
                gap=2,
                wrap=True,
            ),
            mo.callout(
                mo.md("Equal ✓" if _incremental == _recomputed else "**Different ✗**: rows are missing or have the wrong weight."),
                kind="success" if _incremental == _recomputed else "danger",
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With the default changes, turning the switch off breaks the result in two ways:

    * the pair *order 4 + customer `cy`* is missing. Both are new, so only the
      corner term produces it;
    * phantom `bob` rows appear, one with weight **−1**: a row that "exists
      minus one times". The updated order 2 was paired with the *old* `bob`,
      and only the corner term cancels that pairing with `bob`'s deletion.

    Lean proves the full rule once and for all (`ZSet.cross_add`), and goes one
    step further: `Rel.delta` *generates* the delta plan automatically, as an
    ordinary plan that reads the old tables and the change tables, and
    `Rel.delta_correct` proves the generated plan computes exactly the change.
    Since the delta plan is an ordinary plan, a regular engine such as DuckDB
    can run it.

    The fragment covers filter, project, emit, union, cross and inner join.
    Left joins and LIMIT/OFFSET are excluded on purpose: a left join's NULL-padded
    rows must be *retracted* when a match shows up later, and LIMIT depends on
    row order. They need different rules.

    ## 7. What is proven, and what is trusted

    A proof is only as good as what it is about. Here is the honest picture:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.mermaid(
        """
        graph LR
          J["Substrait JSON<br/>(from DuckDB, Ibis, …)"] -->|"parser<br/>TRUSTED · golden tests"| M["Lean model: Rel"]
          M -->|"PROVEN<br/>rewrites, type safety,<br/>incremental rules"| M2["equivalent / delta plan"]
          M2 -->|"engine runs it<br/>TRUSTED · differential tests"| D["DuckDB result"]
          style M fill:#d4f4dd,stroke:#2e8b57
          style M2 fill:#d4f4dd,stroke:#2e8b57
        """
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    * **Proven (green):** everything about the Lean model `Rel`: the rewrites,
      type safety, the incremental rules. Lean checks these mechanically, and
      `#print axioms` confirms no step was skipped.
    * **Trusted, guarded by tests:** the JSON parser (does it translate the plan
      faithfully?) and the engine (does DuckDB behave like the model, e.g. on
      NULLs or integer overflow?). We compare against them with golden tests and,
      next, random differential tests.

    This is the normal shape of verified systems: a small proven core, plus a
    clearly labelled trusted boundary that is tested hard.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.accordion(
        {
            "Glossary": mo.md(r"""
    * **Plan / relation (`Rel`):** a tree of operators: Read, Filter, Project, Emit, Join, …
    * **Semantics (`Rel.eval`):** the reference interpreter that *defines* what a plan means.
    * **Theorem:** a statement quantified over *all* inputs, checked by Lean.
    * **Hypothesis:** a condition a theorem needs (e.g. "the filter only reads old columns").
    * **Well-formed (`Rel.WF`):** every column reference exists and union inputs agree on width.
    * **Bag:** a table where duplicate rows count; order doesn't matter.
    * **Z-set:** a bag where rows carry integer weights; negative means deleted.
    * **Delta (`Δ`):** the change to a table, or to a query result.
    * **Linear operator:** one that handles each row independently, so `Q(A + ΔA) = Q(A) + Q(ΔA)`.
    * **`Perm`:** "same rows, possibly in a different order."
    * **Trusted base:** the parts not covered by proofs (parser, engine).
    """),
            "Where to look in the code": mo.md(r"""
    | Topic | File | Key names |
    |:---|:---|:---|
    | Values, NULL logic | `SubstraitLean/Expr.lean` | `and3`, `isTrue_and3`, `Expr.eval_append` |
    | Operators, meaning, type safety | `SubstraitLean/Rel.lean` | `Rel.eval`, `Rel.WF`, `Rel.eval_arity` |
    | Optimizer rewrites | `SubstraitLean/Rewrites.lean` | `filter_filter`, `filter_project_pushdown` |
    | Executable checker | `SubstraitLean/Check.lean` | `Rel.checkWF`, `checkWF_iff` |
    | Incremental maintenance | `SubstraitLean/Incremental.lean` | `zeval_add`, `delta_correct`, `incremental_sound` |
    | Substrait JSON | `SubstraitLean/Parse.lean` | `parsePlan` |
    """),
            "Try it yourself": mo.md(r"""
    ```bash
    lake build                                    # check every proof
    .lake/build/bin/substrait-check tests/fixtures/virtual_left_join.json
    tests/run.sh                                  # golden tests
    ```

    A good first exercise in Lean: in `Rewrites.lean`, try to prove
    `filter_project_pushdown` **without** the hypothesis `hp`. Lean will get
    stuck exactly where a filter reads a column that only exists after the projection.
    """),
        }
    )
    return


if __name__ == "__main__":
    app.run()
