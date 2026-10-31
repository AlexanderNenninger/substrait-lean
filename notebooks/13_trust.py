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
app = marimo.App(width="medium", app_title="13. What is proved, what is trusted")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 12. [A complete pipeline](?file=12_fitness.py) · [Contents](?file=00_start_here.py) · 14. [DataFusion's surprising semantics](?file=14_datafusion_semantics.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 13. What is proved, what is trusted

    A proof is only as good as what it is about. Every ✅ in this tour is a
    theorem about the Lean model `Rel`. Between your Ibis code and the
    model, and between the model and the engine, there is code that is not
    proved. Here is the honest picture:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.mermaid(
        """
        graph LR
          I["Ibis or SQL"] -->|"Ibis producer, or DataFusion's<br/>for SQL"| J["Substrait JSON"]
          J -->|"parser<br/>TRUSTED · golden tests, round trips"| M["Lean model: Rel"]
          M -->|"PROVED<br/>contracts, keys, runtime errors,<br/>rewrites, update plans"| M2["verdicts,<br/>update plans"]
          M2 -->|"writer, translators, SQL generator<br/>TRUSTED · differential tests"| D["DataFusion · Polars ·<br/>DuckDB · Snowflake"]
          style M fill:#d4f4dd,stroke:#2e8b57
          style M2 fill:#d4f4dd,stroke:#2e8b57
        """
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Proved (green):** everything about `Rel`: the meaning of every
    operator, type safety, the rewrites, the abstract interpreter behind
    contracts, keys and relations between columns, window functions and
    tie-breaking, the absence of runtime errors, composition of contracts,
    the incremental update plans and their weight-column encoding, and the
    chain rule for views over views. Lean checks these mechanically, and
    `#print axioms` in `SubstraitLean/Examples.lean` confirms no step was
    skipped: the proofs use only Lean's three standard axioms.

    **Trusted, guarded by tests:**

    * the JSON **parser** and **writer** (do they translate plans faithfully?)
      and the rewrites the parser does on the way in (`IN` lists, `COALESCE`,
      `RIGHT JOIN`, …), guarded by golden tests and round trips;
    * the column descriptions taken from table **schemas**;
    * **when** DataFusion evaluates an expression (lazy `CASE`, eager `AND`,
      merged filters), which the runtime-error analysis relies on;
    * the `sverify` **glue**: change tables, consolidation, merging;
    * the **Polars translator**, the **SQL generator**, and each **engine**
      itself.

    The randomized tests compare the engines with each other and with
    Lean's `Rel.eval`, compare incremental views with full recomputation,
    check that proved postconditions hold on random data, and check that
    engines only ever fail where an error was reported. They have caught
    real engine bugs: an early version found DuckDB's Substrait reader
    running `UNION ALL` as `UNION DISTINCT`, which is why DuckDB now runs
    generated SQL instead.

    This is the normal shape of verified systems: a small proved core, plus
    a clearly labelled trusted boundary that is tested hard.

    ## What the model doesn't cover yet

    * aggregates (`GROUP BY`, `SUM`, `COUNT`) and framed window aggregates;
    * incremental maintenance of left, semi and anti joins, `DISTINCT`,
      `LIMIT` and windows (pipelines recompute those);
    * relations needing more than "column plus constant", string contents,
      DECIMAL columns, counts across rows;
    * *completeness*: contracts say what every output row satisfies, not
      that no row is lost. The converse is a Lean theorem per plan today
      (`IoT.window_complete` in `SubstraitLean/Completeness.lean`), not
      something the checker reports.
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
    * **Precondition / postcondition:** what a transformation assumes about its inputs / guarantees about its output.
    * **Abstract interpretation:** running a plan on descriptions of values (can it be NULL? which values?) instead of values.
    * **Key:** columns no two rows agree on (`sv.unique`).
    * **Deterministic:** no ties in a window's order, so the engine has no choices to make.
    * **Hoare triple `{P} f {Q}`:** if `P` holds before `f`, `Q` holds after.
    * **Bag:** a table where duplicate rows count; order doesn't matter.
    * **Z-set:** a bag where rows carry integer weights; negative means deleted.
    * **Delta (`Δ`):** the change to a table, or to a query result.
    * **Linear operator:** one that handles each row independently, so `Q(A + ΔA) = Q(A) + Q(ΔA)`.
    * **`Perm`:** "same rows, possibly in a different order."
    * **Trusted base:** the parts not covered by proofs.
    """),
            "Where to look in the code": mo.md(r"""
    | Topic | File | Key names |
    |:---|:---|:---|
    | Values, NULL logic | `SubstraitLean/Expr.lean` | `and3`, `isTrue_and3` |
    | Operators, meaning, type safety | `SubstraitLean/Rel.lean` | `Rel.eval`, `Rel.WF`, `Rel.eval_arity` |
    | Optimizer rewrites | `SubstraitLean/Rewrites.lean` | `filter_filter`, `filter_project_pushdown` |
    | Executable checker | `SubstraitLean/Check.lean` | `Rel.checkWF`, `checkWF_iff` |
    | Contracts | `SubstraitLean/Contracts.lean`, `ContractCheck.lean` | `Rel.aeval_sound`, `contract_sound` |
    | Keys, ties | `SubstraitLean/Keys.lean` | `Rel.keys_sound`, `window_tiebreak` |
    | Windows | `SubstraitLean/Window.lean` | `ROW_NUMBER`, `LAG`, `LEAD`, ranks, `NTILE`, aggregates and `FIRST_VALUE`/`LAST_VALUE`/`NTH_VALUE` over ROWS and RANGE frames |
    | Doubles, time, text | `Float.lean`, `Rounding.lean`, `Time.lean`, `Text.lean` | `round_mono`, `Time.trunc_mono` |
    | Runtime errors | `SubstraitLean/Safety.lean` | `Rel.mayIssues_sound` |
    | Composition, pipelines | `SubstraitLean/Compose.lean` | `Triple.compose`, `Triple.maintained`, `Rel.chain_sound` |
    | Incremental maintenance | `SubstraitLean/Incremental.lean`, `Terms.lean`, `Weighted.lean` | `zeval_add`, `delta_correct`, `weighted_eval` |
    | Substrait JSON | `SubstraitLean/Parse.lean`, `Write.lean` | `parsePlan`, `writePlan` |
    | CLI | `Main.lean` | `substrait-check`, `--write`, `--contract`, `--delta` |
    | Python package | `python/src/sverify/` | `transform`, `verify`, `IncrementalView`, `Pipeline`, `asof_join` |
    | Engines, SQL | `python/src/sverify/polars_engine.py`, `sql/` | `run_plan`, `to_sql` |
    """),
            "Try it yourself": mo.md(r"""
    ```bash
    lake build                     # check every proof (seconds; no Mathlib)
    cd python && uv run poe qa     # proofs, lint, types, golden and Python tests
    ```

    A good first exercise in Lean: in `Rewrites.lean`, try to prove
    `filter_project_pushdown` **without** the hypothesis `hp`. Lean gets
    stuck exactly where a filter reads a column that only exists after the
    projection.
    """),
        }
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    That's the display. The README has the full reference: every proved
    theorem, the modelling choices, and the engine notes.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 12. [A complete pipeline](?file=12_fitness.py) · [Contents](?file=00_start_here.py) · 14. [DataFusion's surprising semantics](?file=14_datafusion_semantics.py) →
    """)
    return


if __name__ == "__main__":
    app.run()
