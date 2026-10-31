"""Pre- and postconditions for transformations, with postconditions proved in Lean.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

    from ibis import _
    import sverify as sv

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.id.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
    )
    def doubled(orders):
        return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

Calling `doubled(orders)` builds the Ibis expression as usual. Before it is
returned, `substrait-check --contract` tries to *prove* every postcondition
from the preconditions, the column types and the transformation itself
(`contract_sound` in `SubstraitLean/Contracts.lean`). An unproved
postcondition raises `VerificationError` that says what Lean could establish,
unless `on_unproved` asks for a runtime check or a warning instead.

Preconditions are assumptions about data that comes from outside, so when the
inputs are bound to a backend they are checked on the data at call time.

Contracted transformations compose. When the result of one feeds another, the
downstream precondition is *proved* from the upstream contract instead of
checked on the data, and the downstream postconditions are proved assuming
only what the upstream one guarantees (`Triple.compose` in
`SubstraitLean/Compose.lean`):

    @sv.transform(
        requires={"orders": [_.amount >= 0, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    doubled(paid(orders))     # `doubled` is proved from `paid`'s guarantees

A link that does not hold raises `CompositionError` naming both sides:
"doubled needs (_.amount >= 0) (it is TRUE or FALSE) on 't'; not_null only
guarantees _.amount.notnull()". Plain Ibis steps in between carry no
guarantees of their own. A composed result can be maintained incrementally
(`sverify.incremental`): its preconditions on the base tables are then
checked on each batch of changes, and its guarantees hold in every state.

Conditions are Ibis expressions (`_.amount >= 0`, or a function of the table)
or SQL snippets (`"amount >= 0"`). SQL snippets are compiled to Substrait by
DataFusion, so they need the `datafusion` extra.

Runtime checks run through Ibis, on the connection the tables are bound to
(`sverify.connect()`), by default; naming an engine (`engine="duckdb"`,
`"polars"` or `"datafusion"`, see `sverify.engines.run`) runs each
condition's plan, as Lean wrote it, there instead, so such conditions must be
inside the Lean model. `unique` checks always run through Ibis.
"""

from __future__ import annotations

import functools
import inspect
import json
import math
import warnings
import weakref
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta
from fractions import Fraction
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.deferred import Deferred
from ibis.common.graph import Node

from sverify.counterexample import Counterexample
from sverify.counterexample import search as search_counterexample
from sverify.engine import (
    Connection,
    Engine,
    connect,
    connection_of,
    create_table,
    plan_json,
    run_checker,
    run_plan,
    to_sql,
    written_plan,
)


def q(name: str) -> str:
    """Quote a SQL identifier."""
    return '"' + name.replace('"', '""') + '"'


@dataclass(frozen=True)
class Unique:
    """No two rows agree on these columns (see `unique`).

    Attributes:
        cols: The key's column names, in the order given to `unique`.
    """

    cols: tuple[str, ...]


def unique(*cols: str) -> Unique:
    """A key: at most one row per combination of `cols`.

    In `requires` it is an assumption about an input (checked on the data when
    the input is bound to a backend); in `ensures` it is proved by
    `Rel.keys_sound` from the input keys and the transformation.

    Args:
        *cols: The names of the key's columns.

    Returns:
        A `Unique` condition, for `requires` or `ensures`.
    """
    return Unique(tuple(cols))


@dataclass(frozen=True)
class References:
    """A foreign key: every non-NULL value of `col` occurs in column `other`
    of table `table` (see `references`).

    Attributes:
        col: The referencing column, in the table the condition is on.
        table: The name of the referenced table.
        other: The referenced column of `table`.
    """

    col: str
    table: str
    other: str


def references(col: str, table: str, other: str) -> References:
    """A foreign key: every non-NULL value of `col` occurs in `table.other`.

    Only for `requires`, where it is checked on the data like `unique` (the
    referenced table must be bound to the same backend). With a key on the
    referenced column it lets `Rel.optimize` turn a left join on it into an
    inner join (`Report.optimized`). Not supported by incremental views.

    Args:
        col: The referencing column of the input the condition is on.
        table: The name of the referenced table, as `verify` and the backend
            know it.
        other: The referenced column of `table`.

    Returns:
        A `References` condition, for `requires`.
    """
    return References(col, table, other)


TableCondition = (Unique, References)
"""Conditions on a whole table, not on each row."""

Condition = (
    Deferred | ir.BooleanValue | str | Unique | References | Callable[[ir.Table], ir.BooleanValue]
)
Transform = ir.Table | str


@dataclass
class CheckedCondition:
    """One postcondition in a `Report`, and what became of its proof."""

    label: str
    """The condition as written, e.g. "(_.amount >= 0)" or "unique(id)"."""
    proved: bool
    """Whether Lean proved it."""
    value: str
    """What Lean established about the condition, e.g. "TRUE or NULL"."""
    counterexample: Counterexample | None = None
    """For an unproved condition: inputs meeting the preconditions on which
    it fails, if the search (`sverify.counterexample`) found one."""


@dataclass(frozen=True)
class Issue:
    """Something that may go wrong when the transformation runs
    (`Rel.mayIssues_sound` in `SubstraitLean/Safety.lean`)."""

    kind: str
    """"division by zero", "overflow", "cast out of range", "negative exponent",
    or "may wrap around" (64-bit overflow of `+`, `-`, `*` or an integer
    `SUM`, which DataFusion does not report)."""
    expr: str
    """The operation, in Lean's notation (`$i` is the operation's i-th input
    column)."""
    error: bool
    """True if DataFusion fails at run time; wrapping around is a warning."""

    def __str__(self) -> str:
        return f"{self.kind}: {self.expr}"


@dataclass
class Report:
    """What Lean proved about a transformation, returned by `verify` and kept
    in `ContractedTransform.last_report`.

    `str(report)` lists each postcondition with its status, the possible
    runtime errors and warnings, and what is known about each output column;
    in a notebook the report renders as tables.
    """

    requires: dict[str, list[str]]
    """The preconditions that were assumed, as labels, per input table."""
    ensures: list[CheckedCondition]
    """Each postcondition, in the order given: its label, whether it was
    proved, what Lean established about it, and a counterexample if one was
    found."""
    facts: dict[str, str] = field(default_factory=dict)
    """What Lean established about each output column."""
    deterministic: bool = True
    """False when rows may tie in a window's ORDER BY: the engine then picks
    an order, and nothing is proved about the result."""
    issues: list[Issue] = field(default_factory=list)
    """Runtime errors and wrap-arounds Lean could not rule out; when empty,
    the transformation provably runs without them."""
    guard_free: bool = False
    """The only issues are integer `SUM`s that may wrap: on data that meets
    the preconditions, the transformation's SQL (`sverify.engines.to_sql`)
    and Polars plan give the same result with `guards=False`, without
    per-row checks (`Rel.guardFree_sound`)."""
    optimized: dict | None = None
    """The transformation as a Substrait JSON plan, rewritten with the facts
    and keys of the preconditions (`Rel.optimize` in
    `SubstraitLean/Semantic.lean`): for example a `DISTINCT` over a key is
    gone. On data that meets the preconditions it gives the same rows
    (`Rel.optimize_sound`); pass it to `sverify.engines.to_sql`, or as JSON
    to `sverify.engines.run`, instead of the transformation. None if Lean
    did not return one."""
    rewrites: list[str] = field(default_factory=list)
    """The rewrites in `optimized`, such as "DISTINCT on a key"."""

    @property
    def proved(self) -> bool:
        """Every postcondition holds and no runtime error is possible."""
        return all(c.proved for c in self.ensures) and not self.errors

    @property
    def errors(self) -> list[Issue]:
        """The `issues` an engine fails on at run time (`Issue.error` is true)."""
        return [i for i in self.issues if i.error]

    @property
    def warnings(self) -> list[Issue]:
        """The `issues` that do not fail but may give a wrong value, such as a
        64-bit wrap-around."""
        return [i for i in self.issues if not i.error]

    @property
    def unproved(self) -> list[CheckedCondition]:
        """The postconditions in `ensures` that were not proved."""
        return [c for c in self.ensures if not c.proved]

    def __str__(self) -> str:
        lines = []
        for table, conds in self.requires.items():
            lines += [f"requires {table}: {c}" for c in conds]
        for c in self.ensures:
            mark = "proved" if c.proved else f"NOT proved (it is {c.value})"
            lines.append(f"ensures {c.label}: {mark}")
            if c.counterexample is not None:
                lines.append(f"  counterexample: {c.counterexample}")
        lines += [f"may fail: {i}" for i in self.errors]
        lines += [f"warning: {i}" for i in self.warnings]
        if not self.deterministic:
            lines.append(f"note: {TIES_HINT}")
        if self.facts:
            lines.append("known about the output:")
            lines += [f"  {name}: {value}" for name, value in self.facts.items()]
        return "\n".join(lines)

    def _repr_markdown_(self) -> str:
        def status(c: CheckedCondition) -> str:
            if c.proved:
                return "✅ proved"
            if c.counterexample is None:
                return f"❌ {c.value}"
            return f"❌ {c.value}; fails on `{c.counterexample}`".replace("|", "\\|")

        rows = [f"| `{c.label}` | {status(c)} |" for c in self.ensures]
        # Issues quote expressions, which may contain `|` (a regex, an OR).
        rows += [f"| runtime | ❌ may fail: {str(i).replace('|', '\\|')} |" for i in self.errors]
        rows += [f"| runtime | ⚠️ {str(i).replace('|', '\\|')} |" for i in self.warnings]
        facts = [f"| `{n}` | {v} |" for n, v in self.facts.items()]
        note = [] if self.deterministic else [f"> ⚠️ {TIES_HINT}", ""]
        return "\n".join(
            [
                *note,
                "| postcondition | status |",
                "|---|---|",
                *rows,
                "",
                "| output column | known values |",
                "|---|---|",
                *facts,
            ]
        )


TIES_HINT = (
    "rows may tie in a window's ORDER BY, so the engine decides their order. "
    "Declare `unique(...)` on the partition and order columns of the input."
)


class VerificationError(Exception):
    """A postcondition, or the absence of runtime errors, could not be proved.

    Import it from `sverify.errors`. The message names each unproved
    postcondition with what Lean established about it, and each possible
    runtime error, followed by the full report.

    Attributes:
        report: The `Report` of the failed proof.
    """

    def __init__(self, report: Report):
        self.report = report
        problems = [f"{c.label} (it is {c.value})" for c in report.unproved]
        problems += [f"no runtime error ({i})" for i in report.errors]
        super().__init__(f"could not prove: {', '.join(problems)}\n{report}")


class PreconditionError(Exception):
    """Input data violates a precondition.

    Import it from `sverify.errors`. Raised when a contracted transformation
    is called on inputs bound to a backend, or a node is refreshed (on the
    full source tables the first time, then on each batch of changes), and a
    precondition does not hold on the rows. The message says how many rows
    violate which condition, for example
    "2 row(s) of orders violate (_.amount >= 0)".
    """


class PostconditionError(Exception):
    """Output data violates a postcondition (only raised by runtime checks).

    Import it from `sverify.errors`. Raised with `on_unproved="runtime"`,
    when a postcondition Lean could not prove fails on the output rows. The
    message says how many output rows violate which condition.
    """


# Doubles, timestamps and dates are integer codes in the Lean model
# (SubstraitLean/Float.lean). A double with magnitude m = |x| * 2^1074 has
# code ±(2m + 1), and zero (-0.0 too) has code 0, which orders codes like SQL
# engines order doubles (-inf < ... < 0.0 < ... < +inf < NaN, one NaN).
# Timestamps are microseconds, dates days.
MAX_MAG = (2**53 - 1) * 2**2045
INF_MAG, NAN_MAG = MAX_MAG + 1, MAX_MAG + 2


def decode_double(code: int) -> float:
    """The double of a code (`FloatCode.toFloat`): zero is `0`, NaN the one NaN."""
    if code == 0:
        return 0.0
    sign = -1.0 if code < 0 else 1.0
    mag = (abs(code) - 1) // 2
    if mag >= NAN_MAG:
        return math.nan
    if mag == INF_MAG:
        return sign * math.inf
    return sign * float(Fraction(mag, 2**1074))


def render_fact(abstract: dict, dtype: Any) -> str | None:
    """Describe a column's abstract value for doubles, timestamps, dates and
    intervals (microseconds); None keeps Lean's own description."""
    rng = abstract.get("int")
    if dtype.is_floating():
        show: Callable[[int], str] = lambda k: repr(decode_double(k))  # noqa: E731
        noun = "a double"
    elif dtype.is_timestamp():
        epoch = datetime(1970, 1, 1)
        show = lambda k: (epoch + timedelta(microseconds=k)).isoformat(sep=" ")  # noqa: E731
        noun = "a timestamp"
    elif dtype.is_date():
        show = lambda k: (date(1970, 1, 1) + timedelta(days=k)).isoformat()  # noqa: E731
        noun = "a date"
    elif dtype.is_interval():
        show = lambda k: str(timedelta(microseconds=k))  # noqa: E731
        noun = "an interval"
    else:
        return None
    parts = []
    if rng is not None:
        lo = None if rng["lo"] is None else int(rng["lo"])
        hi = None if rng["hi"] is None else int(rng["hi"])
        if not dtype.is_floating():
            # Bounds near the 64-bit limits go without saying (as in Lean's text).
            lo = None if lo is not None and lo <= -(2**60) else lo
            hi = None if hi is not None and hi >= 2**60 else hi
        if lo is None and hi is None:
            parts.append(f"any {noun.split()[-1]}")
        elif lo is not None and hi is not None and lo == hi:
            parts.append(f"{noun} = {show(lo)}")
        elif dtype.is_floating():
            # Codes are 0 and odd numbers of magnitude 3 or more; a bound
            # between two codes reads best against its neighbour, zero first.
            def valid(k: int) -> bool:
                return k == 0 or (k % 2 == 1 and abs(k) >= 3)

            def up(k: int) -> int:
                """The smallest code ≥ k."""
                return k if valid(k) else 0 if k in (-2, -1) else 3 if k in (1, 2) else k + 1

            def down(k: int) -> int:
                """The largest code ≤ k."""
                return k if valid(k) else 0 if k in (1, 2) else -3 if k in (-2, -1) else k - 1

            def ge(k: int) -> str:
                n = up(k)
                return f"≥ {show(n)}" if n in (k, 0) else f"> {show(down(k - 1))}"

            def le(k: int) -> str:
                p = down(k)
                return f"≤ {show(p)}" if p in (k, 0) else f"< {show(up(k + 1))}"

            if hi is None:
                parts.append(f"{noun} {ge(lo)}")  # type: ignore[arg-type]
            elif lo is None:
                parts.append(f"{noun} {le(hi)}")
            else:
                parts.append(f"{noun} {ge(lo)} and {le(hi)}")
        elif hi is None:
            parts.append(f"{noun} ≥ {show(lo)}")  # type: ignore[arg-type]
        elif lo is None:
            parts.append(f"{noun} ≤ {show(hi)}")
        else:
            parts.append(f"{noun} in [{show(lo)}, {show(hi)}]")
    if abstract.get("null"):
        parts.append("NULL")
    return " or ".join(parts) if parts else "nothing (no rows)"


def label(cond: Condition) -> str:
    if isinstance(cond, Unique):
        return f"unique({', '.join(cond.cols)})"
    if isinstance(cond, References):
        return f"references({cond.col}, {cond.table}.{cond.other})"
    if isinstance(cond, str):
        return cond
    if isinstance(cond, Deferred):
        return repr(cond)
    return getattr(cond, "__name__", repr(cond))


def column_names(schema: ibis.Schema) -> list[str]:
    return [name for name, _ in schema.items()]


def leaf_tables(expr: ir.Table) -> dict[str, ibis.Schema]:
    leaves = expr.op().find((ops.UnboundTable, ops.DatabaseTable))
    return {t.name: t.schema for t in leaves if isinstance(t, ops.UnboundTable | ops.DatabaseTable)}


def resolve(cond: Condition, table: ir.Table) -> ir.BooleanValue:
    if isinstance(cond, Deferred):
        return cond.resolve(table)
    if callable(cond):
        return cond(table)
    return cond  # type: ignore[return-value]


def condition_query(table: Transform, cond: Condition) -> Transform:
    """A query selecting one condition column from a table or transformation:
    SQL for SQL conditions, an Ibis expression otherwise."""
    if isinstance(cond, str):
        source = table if isinstance(table, str) else to_sql(table)
        return f'SELECT ({cond}) AS "c" FROM ({source}) AS "t"'
    if isinstance(table, str):
        raise TypeError("Ibis conditions need an Ibis transformation; use a SQL string instead")
    return table.select(c=resolve(cond, table))


def verify(
    transform: Transform,
    *,
    requires: Mapping[str, Sequence[Condition]] | None = None,
    ensures: Sequence[Condition] = (),
    tables: Mapping[str, ibis.Schema | ir.Table] | None = None,
    counterexamples: int = 200,
) -> Report:
    """Try to prove `ensures` about `transform` (an Ibis table expression or a
    SQL query) from `requires`, a mapping from table name to conditions.

    `tables` gives the input schemas; it is only needed for SQL transforms.
    For each unproved postcondition, up to `counterexamples` small inputs are
    tried for one that breaks it (`sverify.counterexample`); 0 skips that.

    A proof is about the plan `transform` compiles to, under `Rel.eval`. An
    Ibis expression compiles with sverify's own producer, so it means what
    `docs/ibis-semantics.md` says, whichever Ibis backend it came from; where
    Ibis backends disagree (`%` on Polars, `-0.0 == 0.0` on DataFusion, …),
    no backend's `execute` is guaranteed to match. `sverify.engines.run`
    runs the verified plan with that meaning (or fails) on DataFusion, DuckDB and
    Polars. A SQL string means what the SQL producer (DataFusion's or
    Isthmus) makes of it.

    Unlike `transform`, `verify` checks nothing on data and raises nothing
    when a postcondition is unproved: it returns the report.

    Args:
        transform: The transformation, as an Ibis table expression or a SQL
            query.
        requires: Preconditions, as a mapping from input table name to its
            conditions (Ibis expressions, SQL snippets, `unique` or
            `references`). They are assumed, not checked. Default: none.
        ensures: Postconditions on the output to prove, including `unique`
            keys. Default: none, which still reports the facts and possible
            runtime errors.
        tables: Input schemas by table name, as Ibis schemas, anything
            `ibis.schema` accepts, or Ibis tables. Needed for SQL transforms;
            an Ibis expression's own tables are found from it.
        counterexamples: How many small inputs to try per unproved
            postcondition when searching for one that breaks it. Default 200;
            0 skips the search.

    Returns:
        A `Report` with the status of each postcondition, the possible
        runtime errors, and what is known about each output column.

    Raises:
        ValueError: `unique` or `references` names an unknown column or
            table, or the checker fails on the request (for example on a plan
            outside the Lean model).
        TypeError: An Ibis condition is given for a SQL transform.

    Examples:
        A SQL query, with its input schema (compiling SQL needs the
        `datafusion` extra, or Isthmus):

        ```python
        import ibis
        import sverify as sv
        from ibis import _

        orders = ibis.table({"id": "int64", "amount": "int64"}, name="orders")

        report = sv.verify(
            "select id, amount from orders where amount > 0",
            tables={"orders": orders},
            ensures=["amount > 0"],
        )
        report.proved  # True
        ```

        An Ibis expression, with preconditions:

        ```python
        report = sv.verify(
            orders.select(orders.id, total=orders.amount + 1),
            requires={"orders": [_.amount >= 0]},
            ensures=[_.total >= 1],
        )
        report.facts["total"]  # 'an integer ≥ 1'
        ```
    """
    schemas = {
        name: s.schema() if isinstance(s, ir.Table) else ibis.schema(s)
        for name, s in (tables or {}).items()
    }
    if not isinstance(transform, str):
        schemas = {**leaf_tables(transform), **schemas}
    requires = requires or {}
    con = connect()
    for name, schema in schemas.items():
        create_table(con, name, schema)

    def plan(query: Transform) -> Any:
        return json.loads(plan_json(con, query))

    def table_ref(name: str) -> Transform:
        return f"SELECT * FROM {q(name)}" if isinstance(transform, str) else con.table(name)

    req_conds = [
        (t, c) for t, cs in requires.items() for c in cs if not isinstance(c, TableCondition)
    ]
    req_plans = [plan(condition_query(table_ref(t), c)) for t, c in req_conds]
    ens_plans = []
    for c in ensures:
        if isinstance(c, TableCondition):
            continue
        p = plan(condition_query(transform, c))
        p["relations"][0]["root"]["names"] = [label(c)]
        ens_plans.append(p)
    transform_plan = plan(transform)
    out_cols: list[str] = transform_plan["relations"][0]["root"]["names"]

    def positions(cols: Sequence[str], names: Sequence[str]) -> list[int]:
        missing = [c for c in cols if c not in names]
        if missing:
            raise ValueError(f"unique() names unknown columns: {missing}")
        return [list(names).index(c) for c in cols]

    keys = {
        t: [positions(c.cols, column_names(schemas[t])) for c in cs if isinstance(c, Unique)]
        for t, cs in requires.items()
    }
    ensures_keys = [positions(c.cols, out_cols) for c in ensures if isinstance(c, Unique)]

    def foreign_key(t: str, c: References) -> list:
        if c.table not in schemas:
            raise ValueError(f"references() names an unknown table: {c.table!r}")
        [col] = positions([c.col], column_names(schemas[t]))
        [other] = positions([c.other], column_names(schemas[c.table]))
        return [col, c.table, other]

    foreign_keys = {
        t: [foreign_key(t, c) for c in cs if isinstance(c, References)]
        for t, cs in requires.items()
    }
    contract = {
        "requires": req_plans,
        "ensures": ens_plans,
        "transform": transform_plan,
        "keys": keys,
        "ensures_keys": ensures_keys,
        "references": foreign_keys,
    }

    code, stdout, stderr = run_checker(("--contract",), json.dumps(contract))
    if code not in (0, 4):
        raise ValueError(f"substrait-check --contract failed: {stderr.strip()}")
    out = json.loads(stdout)
    dtypes = {} if isinstance(transform, str) else dict(transform.schema().items())

    def describe(f: dict) -> str:
        dtype = dtypes.get(f["name"])
        return (render_fact(f["abstract"], dtype) if dtype is not None else None) or f["value"]

    rows = iter(out["ensures"])
    key_results = iter(out["keys"])
    req_named = [(t, p) for (t, _), p in zip(req_conds, req_plans, strict=True)]
    ens_iter = iter(ens_plans)
    key_iter = iter(ensures_keys)

    def find(target: dict | Sequence[int]) -> Counterexample | None:
        if not counterexamples:
            return None
        return search_counterexample(
            schemas,
            req_named,
            keys,
            transform_plan,
            target,
            budget=counterexamples,
            references=foreign_keys,
        )

    checked = []
    for c in ensures:
        if isinstance(c, Unique):
            ok = next(key_results)["proved"]
            value = (
                "a key"
                if ok
                else "not shown to be a key"
                if out["deterministic"]
                else "undetermined: rows may tie in a window's ORDER BY"
            )
            cols = next(key_iter)
            cex = None if ok else find(cols)
            checked.append(CheckedCondition(label(c), ok, value, cex))
        elif isinstance(c, References):
            checked.append(CheckedCondition(label(c), False, "foreign keys are not proved"))
        else:
            e = next(rows)
            p = next(ens_iter)
            cex = None if e["proved"] else find(p)
            checked.append(CheckedCondition(e["name"], e["proved"], e["value"], cex))
    return Report(
        requires={t: [label(c) for c in cs] for t, cs in requires.items()},
        ensures=checked,
        facts={f["name"]: describe(f) for f in out["facts"]},
        deterministic=out["deterministic"],
        issues=[Issue(i["kind"], i["expr"], i["error"]) for i in out["issues"]],
        guard_free=out["guard_free"],
        optimized=out["optimized"],
        rewrites=out["rewrites"],
    )


def violations(table: ir.Table, cond: Condition, engine: Engine | None = None) -> int:
    """Rows of a bound table where `cond` is not TRUE (FALSE or NULL), or for
    `unique`, rows beyond the first for each repeated key.

    With an engine named, the condition's plan runs there, over the tables of
    the connection `table` is bound to; otherwise Ibis counts on that
    connection."""
    if not isinstance(cond, TableCondition) and engine is not None:
        con = connection_of(table)
        if con is None:
            raise ValueError("checking a condition on an engine needs a table of sverify.connect()")
        plan = written_plan(plan_json(con, condition_query(table, cond)))
        return sum(v is not True for v in run_plan(con, plan, engine).column(0).to_pylist())
    if isinstance(cond, References):
        other = ibis.get_backend(table).table(cond.table)
        present = table.filter(table[cond.col].notnull())
        missing: Any = present.anti_join(other, [present[cond.col] == other[cond.other]]).count()
        return int(missing.execute())
    if isinstance(cond, Unique):
        total: Any = table.count()
        distinct: Any = table.select(*cond.cols).distinct().count()
        return int(total.execute()) - int(distinct.execute())
    if isinstance(cond, str):
        backend: Any = ibis.get_backend(table)
        sql = ibis.to_sql(table, dialect=backend.name)
        query = f'SELECT count(*) FROM ({sql}) AS "t" WHERE NOT coalesce(({cond}), FALSE)'
        # On the backend's own connection: Ibis 12's `backend.sql` asks DuckDB 2
        # for the query's schema with a method it no longer has.
        # `raw_sql` returns the connection itself: fetch every row, so that it
        # is free for the next query, and leave it open.
        return int(backend.raw_sql(query).fetchall()[0][0])
    count: Any = table.filter(~resolve(cond, table).fill_null(ibis.literal(False))).count()
    return int(count.execute())


@dataclass(frozen=True)
class Fact:
    """What table metadata says about every row of a table, as a SQL
    condition, and where it comes from ("Delta constraint", "file stats @v3").
    The metadata is trusted; facts only discharge preconditions through Lean
    (`contract_sound` on the table itself), never by name."""

    condition: str
    source: str


SCHEMA = "schema"
ON_DATA = "checked on data"


@dataclass(frozen=True)
class Discharged:
    """How a precondition on a table was established: proved from its
    `SCHEMA`, proved from facts of one metadata source, or `ON_DATA`."""

    table: str
    condition: str
    source: str

    def __str__(self) -> str:
        return f"{self.table}: {self.condition} ({self.source})"


# Metadata facts of tables read from a table format (`sverify.io`), keyed
# by backend identity and table name. Tables without an entry only have
# their preconditions checked on the data: an in-memory schema is not enforced.
_facts: dict[tuple[int, str], list[Fact]] = {}


def register_facts(con: Connection, name: str, facts: Sequence[Fact] | None) -> None:
    """Record (or with None, forget) what metadata says about table `name`."""
    key = (id(con.ibis), name)
    if facts is None:
        _facts.pop(key, None)
    else:
        _facts[key] = list(facts)


def table_facts(table: ir.Table) -> list[Fact] | None:
    """Metadata facts of a base table, if it was read from a table format."""
    op = table.op()
    if not isinstance(op, ops.DatabaseTable):
        return None
    return _facts.get((id(op.source), op.name))


_proved_from: dict[tuple, frozenset[str]] = {}


def _prove_from(table: ir.Table, facts: Sequence[str], conds: Sequence[Condition]) -> set[str]:
    """Labels of `conds` that Lean proves about every row of `table` from its
    schema and `facts`. A fact the checker cannot read proves nothing."""
    name = table.op().name  # type: ignore[attr-defined]
    key = (name, str(table.schema()), tuple(facts), tuple(label(c) for c in conds))
    if key not in _proved_from:
        try:
            report = verify(table, requires={name: list(facts)}, ensures=conds, counterexamples=0)
            _proved_from[key] = frozenset(c.label for c in report.ensures if c.proved)
        except Exception:
            _proved_from[key] = frozenset()
    return set(_proved_from[key])


def discharge(
    table: ir.Table,
    name: str,
    conds: Sequence[Condition],
    engine: Engine | None,
    facts: Sequence[Fact] | None,
    what: str,
) -> list[Discharged]:
    """Establish row conditions on a bound table, reported under `name`.

    With metadata `facts`, each condition is proved from the schema alone if
    possible, else from the schema and the facts of the first sources (in
    order) that suffice. The rest are checked on the data, raising
    `PreconditionError` with "<n> <what> violate <condition>"."""
    out: list[Discharged] = []
    todo = list(conds)
    if facts is not None:
        stages: dict[str, list[str]] = {SCHEMA: []}
        for f in facts:
            stages.setdefault(f.source, []).append(f.condition)
        assumed: list[str] = []
        for source, extra in stages.items():
            rowwise = [c for c in todo if not isinstance(c, TableCondition)]
            if not rowwise:
                break
            assumed += extra
            proved = _prove_from(table, assumed, rowwise)
            out += [Discharged(name, label(c), source) for c in rowwise if label(c) in proved]
            todo = [c for c in todo if label(c) not in proved]
    for c in todo:
        if n := violations(table, c, engine):
            raise PreconditionError(f"{n} {what} violate {label(c)}")
        out.append(Discharged(name, label(c), ON_DATA))
    return out


def is_bound(table: ir.Table) -> bool:
    try:
        ibis.get_backend(table)
    except Exception:
        return False
    return True


class CompositionError(VerificationError):
    """A contracted transformation's precondition on an input is not implied
    by what the contracted transformation producing that input guarantees.

    Import it from `sverify.errors`. It is raised when the link is built:
    when a transform is called on another contracted transformation's result,
    or on a node (`sverify.Node`) built from one, stored or not. The message
    names both sides, for example "doubled needs (_.amount >= 0) (it is TRUE
    or FALSE) on 't'; not_null only guarantees _.amount.notnull()". With
    `on_unproved="runtime"` and a bound input, the precondition is checked on
    the data instead; with `on_unproved="warn"` it is a warning.

    Attributes:
        report: The `Report` of the failed proof of the link.
        consumer: The name of the transformation whose precondition failed.
        param: The parameter of `consumer` that received the input.
        producer: The name of the contracted transformation that produced it.
    """

    def __init__(self, report: Report, consumer: str, param: str, producer: str, guarantees):
        self.report = report
        self.consumer, self.param, self.producer = consumer, param, producer
        needs = ", ".join(f"{c.label} (it is {c.value})" for c in report.unproved)
        given = ", ".join(guarantees) or "nothing"
        Exception.__init__(
            self,
            f"{consumer} needs {needs} on {param!r}; {producer} only guarantees {given}",
        )


@dataclass(frozen=True)
class Provenance:
    """How a contracted result was made, kept so that a later contracted
    transformation (or an incremental view) can build on its guarantees.

    `body` is the result with every contracted or derived input replaced by a
    placeholder table; `assumptions` are what the proof of `body` assumed about
    each of its tables. The result satisfies `guarantees` whenever the base
    tables satisfy `external`."""

    transform: ContractedTransform
    body: ir.Table
    assumptions: dict[str, list[Condition]]
    guarantees: list[Condition]
    report: Report
    external: dict[str, list[Condition]]
    """Preconditions on base tables, of this transformation and every
    contracted transformation upstream."""
    unproved_links: list[str]
    """Preconditions on derived inputs that were checked on the data, or
    merely warned about, instead of proved."""


# Keyed by identity: Ibis ops compare by structure, and an equal expression
# built independently has not been through the contract's checks.
_provenance: dict[int, tuple[weakref.ref[Node], Provenance]] = {}


def _lookup(op: Node) -> Provenance | None:
    entry = _provenance.get(id(op))
    return entry[1] if entry is not None and entry[0]() is op else None


def _register(op: Node, prov: Provenance) -> None:
    key = id(op)
    _provenance[key] = (weakref.ref(op, lambda _, reg=_provenance: reg.pop(key, None)), prov)


def provenance(table: ir.Table) -> Provenance | None:
    """The contract behind `table`, if a contracted transformation returned it."""
    return _lookup(table.op())


def _is_base(op: Node) -> bool:
    return isinstance(op, ops.UnboundTable | ops.DatabaseTable)


def _merge(into: dict[str, list[Condition]], extra: Mapping[str, Sequence[Condition]]) -> None:
    for t, cs in extra.items():
        have = into.setdefault(t, [])
        have += [c for c in cs if label(c) not in {label(h) for h in have}]


def _fresh(name: str, taken: set[str]) -> str:
    out, n = name, 1
    while out in taken:
        n += 1
        out = f"{name}_{n}"
    taken.add(out)
    return out


@dataclass
class _Abstraction:
    """An expression with its contracted parts replaced by placeholder tables
    (assume-guarantee reasoning: a contracted result is only known by its
    guarantees)."""

    body: ir.Table
    assumptions: dict[str, list[Condition]]
    external: dict[str, list[Condition]]
    unproved_links: list[str]


def _abstract(
    expr: ir.Table,
    placeholders: Mapping[Node, tuple[str, list[Condition]]] | None = None,
    taken: set[str] | None = None,
) -> _Abstraction:
    """Replace `placeholders` (op -> table name and its assumptions) and every
    other contracted result inside `expr` by placeholder tables."""
    placeholders = dict(placeholders or {})
    given = set(placeholders)
    taken = set(leaf_tables(expr)) | {n for n, _ in placeholders.values()} | (taken or set())
    for op in expr.op().find(lambda n: _lookup(n) is not None):
        prov = _lookup(op)
        if prov is not None and op not in placeholders and op is not expr.op():
            placeholders[op] = (_fresh(prov.transform.name, taken), list(prov.guarantees))
    mapping: dict[Node, Node] = {
        op: ibis.table(op.to_expr().schema(), name=name).op()  # type: ignore[attr-defined]
        for op, (name, _) in placeholders.items()
    }
    root = expr.op()
    body: ir.Table = (mapping[root] if root in mapping else root.replace(mapping)).to_expr()  # type: ignore[attr-defined]
    used = set(leaf_tables(body))
    out = _Abstraction(body, {}, {}, [])
    for op, (name, conds) in placeholders.items():
        if name in used and conds:
            _merge(out.assumptions, {name: conds})
        if name in used and op not in given and (prov := _lookup(op)):
            _merge(out.external, prov.external)
            out.unproved_links += prov.unproved_links
    return out


@dataclass
class ViewContract:
    """The contract of a (possibly composed) contracted expression, as seen by
    an incremental view: it `guarantees` its proved postconditions on every
    state whose base tables satisfy `requires`."""

    requires: dict[str, list[Condition]]
    guarantees: list[Condition]
    provenance: Provenance | None


def view_contract(expr: ir.Table) -> ViewContract:
    """Collect the base-table preconditions of every contracted
    transformation inside `expr`. Refuses preconditions on derived inputs that
    were checked on data instead of proved: a view could not keep them true
    from base-table changes."""
    prov = _lookup(expr.op())
    if prov is not None:
        requires, unproved = prov.external, prov.unproved_links
    else:
        inner = _abstract(expr)
        requires, unproved = inner.external, inner.unproved_links
    if unproved:
        raise ValueError(
            "cannot maintain incrementally: preconditions on derived inputs were "
            f"not proved ({'; '.join(unproved)})"
        )
    return ViewContract(
        {t: list(cs) for t, cs in requires.items()},
        list(prov.guarantees) if prov else [],
        prov,
    )


def register_view(table: ir.Table, contract: ViewContract) -> None:
    """Let contracted transformations that read a materialized view `table`
    build on the guarantees of the expression it materializes."""
    if contract.provenance is not None:
        _register(table.op(), contract.provenance)


class ContractedTransform:
    """A transformation with a contract; see `transform`.

    Call it like the function it wraps. Called on Ibis tables, it returns the
    same Ibis expression, after proving the contract. Called on sources
    (`sverify.io`) or nodes, it returns a `sverify.Node`, whose contract is
    checked when it is built. It keeps the wrapped function's name and
    docstring.

    Attributes:
        name: The wrapped function's name; also the name of the nodes it
            builds.
    """

    def __init__(
        self,
        fn: Callable[..., ir.Table],
        requires: Mapping[str, Sequence[Condition]],
        ensures: Sequence[Condition],
        on_unproved: Literal["error", "runtime", "warn"],
        check_requires: bool,
        engine: Engine | None,
    ):
        self.fn, self.requires, self.ensures = fn, requires, ensures
        self.on_unproved, self.check_requires = on_unproved, check_requires
        self.engine = engine
        self.name: str = fn.__name__
        self.signature = inspect.signature(fn)
        unknown = set(requires) - set(self.signature.parameters)
        if unknown:
            raise TypeError(f"requires names unknown parameters: {sorted(unknown)}")
        self.last_report: Report | None = None
        """The `Report` of the proof of the postconditions in the last call,
        or None before the first call."""
        self.last_preconditions: list[Discharged] = []
        """How each precondition on a bound input was established, in the
        last call: from metadata (`sverify.io` tables) or on the data."""
        self._cache: dict[tuple, Report] = {}
        functools.update_wrapper(self, fn)

    def _verify(
        self, body: ir.Table, assumptions: Mapping[str, Sequence[Condition]], ensures, tag: str
    ) -> Report:
        key = (
            tag,
            to_sql(body),
            tuple(sorted((n, str(s)) for n, s in leaf_tables(body).items())),
            tuple(sorted((t, tuple(label(c) for c in cs)) for t, cs in assumptions.items())),
            tuple(label(c) for c in ensures),
        )
        if key not in self._cache:
            self._cache[key] = verify(body, requires=assumptions, ensures=ensures)
        return self._cache[key]

    def _check_on_data(self, table: ir.Table, param: str, conds: Sequence[Condition]) -> bool:
        """Establish preconditions on a bound input, from its metadata where
        possible (`discharge`); False if it is not bound."""
        if not is_bound(table):
            return False
        self.last_preconditions += discharge(
            table, param, conds, self.engine, table_facts(table), f"row(s) of {param}"
        )
        return True

    def _link(self, param: str, value: ir.Table, conds: list[Condition]) -> _Abstraction:
        """Discharge this transformation's preconditions on a derived input by
        proving them from what produced it (assume-guarantee composition).
        Returns, as `assumptions`, what may be assumed about the input."""
        prov = _lookup(value.op())
        if prov is not None:
            inner = _Abstraction(
                prov.body, prov.assumptions, prov.external, list(prov.unproved_links)
            )
            known = list(prov.guarantees)
        else:
            # A plain Ibis expression guarantees nothing by itself, but its
            # obligations may still follow from its operations.
            inner, known = _abstract(value), []
        needed = [c for c in conds if label(c) not in {label(k) for k in known}]
        out = _Abstraction(value, {param: known + needed}, inner.external, inner.unproved_links)
        if not needed:
            return out
        report = self._verify(inner.body, inner.assumptions, needed, f"link {param}")
        proved = {c.label for c in report.ensures if c.proved}
        unproved = [c for c in needed if label(c) not in proved]
        if not unproved:
            return out
        out.unproved_links += [f"{self.name}: {label(c)} on {param}" for c in unproved]
        if prov is None:
            # Like a base table: checked on the data when it is bound, else assumed.
            if self.check_requires:
                self._check_on_data(value, param, unproved)
            return out
        error = CompositionError(
            report, self.name, param, prov.transform.name, [label(c) for c in known]
        )
        if self.on_unproved == "warn":
            warnings.warn(str(error), stacklevel=3)
        elif not (self.on_unproved == "runtime" and self._check_on_data(value, param, unproved)):
            raise error
        return out

    def __call__(self, *args, **kwargs) -> Any:
        """Build the result and prove the contract.

        When an input is a source (`sverify.io`) or a node, the result is a
        `sverify.Node`. The contract is checked then, on placeholder tables
        with the inputs' schemas: the postconditions are proved, and a
        precondition on another node's result must follow from what that
        node guarantees. Preconditions on sources are checked on the data
        when the node is refreshed, and then on every batch.

        Otherwise the result is the Ibis expression the wrapped function
        returns. Inputs bound to a backend have their preconditions checked
        on the data (or proved from table metadata); results of other
        contracted transformations have them proved from those
        transformations' guarantees. Then the postconditions are proved.

        Args:
            *args: The wrapped function's positional arguments: Ibis tables,
                or sources and nodes (not a mix of both).
            **kwargs: The wrapped function's keyword arguments, likewise.

        Returns:
            A `sverify.Node` if an input is a source or a node, else the Ibis
            table expression the wrapped function returns.

        Raises:
            PreconditionError: A bound input's data violates a precondition.
            CompositionError: A precondition on another contracted
                transformation's result does not follow from its guarantees.
            VerificationError: A postcondition, or the absence of runtime
                errors, could not be proved (with `on_unproved="error"`, or
                with `"runtime"` when the result is not bound).
            PostconditionError: With `on_unproved="runtime"`, an unproved
                postcondition fails on the output data.
            TypeError: Sources or nodes are mixed with Ibis tables.
            ValueError: The node would read two tables of the same name.
        """
        from sverify import nodes

        if nodes.wants_node(args, kwargs):
            return nodes.derive(self, args, kwargs)
        inputs = self.signature.bind(*args, **kwargs).arguments
        self.last_preconditions = []
        result = self.fn(*args, **kwargs)
        placeholders: dict[Node, tuple[str, list[Condition]]] = {}
        base: dict[str, list[Condition]] = {}
        external: dict[str, list[Condition]] = {}
        unproved_links: list[str] = []
        taken = set(leaf_tables(result))
        for param, value in inputs.items():
            if not isinstance(value, ir.Table):
                continue
            conds = list(self.requires.get(param, ()))
            op = value.op()
            if _is_base(op) and _lookup(op) is None:
                # Data from outside: checked when bound to a backend.
                _merge(base, {op.name: conds})  # type: ignore[attr-defined]
                if self.check_requires:
                    self._check_on_data(value, param, conds)
                continue
            link = self._link(param, value, conds)
            _merge(external, link.external)
            unproved_links += link.unproved_links
            if op in placeholders:  # the same input under two parameters
                name, assumed = placeholders[op]
                _merge({name: assumed}, {name: link.assumptions[param]})
            else:
                prov = _lookup(op)
                name = _fresh(prov.transform.name if prov else param, taken)
                placeholders[op] = (name, link.assumptions[param])
        abstraction = _abstract(result, placeholders, taken)
        assumptions = {**abstraction.assumptions}
        _merge(assumptions, base)
        report = self.last_report = self._verify(
            abstraction.body, assumptions, self.ensures, "ensures"
        )
        if not report.proved:
            if self.on_unproved == "warn":
                warnings.warn(str(VerificationError(report)), stacklevel=2)
            # Runtime errors cannot be checked on the data beforehand: in
            # "runtime" mode the engine raises them if they happen.
            elif self.on_unproved == "runtime" and is_bound(result):
                unproved = {c.label for c in report.unproved}
                for c in self.ensures:
                    if label(c) in unproved and (n := violations(result, c, self.engine)):
                        raise PostconditionError(f"{n} output row(s) violate {label(c)}")
            else:
                raise VerificationError(report)
        _merge(external, abstraction.external)
        _merge(external, base)
        proved = {c.label for c in report.ensures if c.proved}
        _register(
            result.op(),
            Provenance(
                transform=self,
                body=abstraction.body,
                assumptions=assumptions,
                guarantees=[c for c in self.ensures if label(c) in proved],
                report=report,
                external=external,
                unproved_links=unproved_links + abstraction.unproved_links,
            ),
        )
        return result


def transform(
    requires: Mapping[str, Sequence[Condition]] | None = None,
    ensures: Sequence[Condition] = (),
    *,
    on_unproved: Literal["error", "runtime", "warn"] = "error",
    check_requires: bool = True,
    engine: Engine | None = None,
) -> Callable[[Callable[..., ir.Table]], ContractedTransform]:
    """Decorate a function from Ibis tables to an Ibis table with a contract.

    `requires` maps parameter names to conditions on that input. On each call
    the postconditions are proved (cached per input schema and expression) and
    the report is kept in `.last_report`; see the module docstring. With
    `on_unproved="runtime"`, unproved postconditions are checked on the output
    data instead, which needs inputs bound to a connection. `engine` says where
    those checks on data run (see the module docstring).

    Called on sources (`sverify.io`) or nodes, the transform builds a
    `sverify.Node` instead of an Ibis expression: transforms compose over
    sources, `.write(sink)` stores a result, and `refresh` keeps it up to
    date (see `sverify.Node`).

    Args:
        requires: Preconditions, as a mapping from parameter name to
            conditions on that input: Ibis expressions (`_.amount >= 0`),
            functions of the table, SQL snippets (`"amount >= 0"`), `unique`
            or `references`. Default: none.
        ensures: Postconditions on the result, in the same forms (but not
            `references`). Default: none, which still rules out runtime
            errors.
        on_unproved: What happens when a postcondition, or a precondition on
            another contracted transformation's result, is not proved:
            `"error"` (the default) raises; `"runtime"` checks it on the data
            instead, which needs bound inputs; `"warn"` emits a warning and
            returns the result.
        check_requires: Whether to check preconditions on the data of bound
            inputs at call time. Default True.
        engine: Where checks on data run: `"duckdb"`, `"polars"` or
            `"datafusion"` run each condition's plan as Lean wrote it; None
            (the default) runs them through Ibis on the inputs' connection.

    Returns:
        A decorator that turns the function into a `ContractedTransform`.

    Raises:
        TypeError: When decorating, if `requires` names a parameter the
            function does not have. Calls raise `PreconditionError`,
            `CompositionError`, `VerificationError` or `PostconditionError`
            from `sverify.errors` (see `ContractedTransform.__call__`).

    Examples:
        A contract that holds, on a source, and what Lean worked out about
        the output:

        ```python
        import pyarrow as pa
        import sverify as sv
        from ibis import _
        from sverify.io import StaticSource

        orders = StaticSource(
            pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders"
        )

        @sv.transform(
            requires={"orders": [_.amount >= 0, _.id.notnull()]},
            ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
        )
        def doubled(orders):
            return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

        big = doubled(orders)  # a Node, proved here
        doubled.last_report.proved  # True
        doubled.last_report.facts["doubled"]  # 'an integer ≥ 22'
        big.refresh()
        big.to_arrow().to_pylist()  # [{'id': 1, 'doubled': 60}]
        ```

        Transforms compose: the downstream precondition is proved from the
        upstream guarantee, and a link that does not hold is refused:

        ```python
        from sverify.errors import CompositionError

        @sv.transform(requires={"t": [_.doubled >= 0]}, ensures=[_.plus >= 1])
        def plus_one(t):
            return t.select(t.id, plus=t.doubled + 1)

        plus_one(big)  # proved from what doubled guarantees

        @sv.transform(requires={"t": [_.doubled >= 100]})
        def huge(t):
            return t

        try:
            huge(big)
        except CompositionError as e:
            print(str(e).split(";")[0])
        # huge needs (_.doubled >= 100) (it is TRUE or FALSE) on 't'
        ```

        A postcondition that does not follow is refused:

        ```python
        from sverify.errors import VerificationError

        @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
        def total(orders):
            return orders.select(orders.id, total=orders.amount + 1)

        try:
            total(orders)
        except VerificationError as e:
            print(str(e).splitlines()[0])
        # could not prove: (_.total > 5) (it is TRUE or FALSE)
        ```
    """
    return lambda fn: ContractedTransform(
        fn, requires or {}, ensures, on_unproved, check_requires, engine
    )
