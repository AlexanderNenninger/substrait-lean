"""Pre- and postconditions for transformations, with postconditions proved in Lean.

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
`"polars"` or `"datafusion"`, see `sverify.engine.run_plan`) runs each
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
    """No two rows agree on these columns (see `unique`)."""

    cols: tuple[str, ...]


def unique(*cols: str) -> Unique:
    """A key: at most one row per combination of `cols`.

    In `requires` it is an assumption about an input (checked on the data when
    the input is bound to a backend); in `ensures` it is proved by
    `Rel.keys_sound` from the input keys and the transformation.
    """
    return Unique(tuple(cols))


Condition = Deferred | ir.BooleanValue | str | Unique | Callable[[ir.Table], ir.BooleanValue]
Transform = ir.Table | str


@dataclass
class CheckedCondition:
    label: str
    proved: bool
    value: str
    """What Lean established about the condition, e.g. "TRUE or NULL"."""


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
    requires: dict[str, list[str]]
    ensures: list[CheckedCondition]
    facts: dict[str, str] = field(default_factory=dict)
    """What Lean established about each output column."""
    deterministic: bool = True
    """False when rows may tie in a window's ORDER BY: the engine then picks
    an order, and nothing is proved about the result."""
    issues: list[Issue] = field(default_factory=list)
    """Runtime errors and wrap-arounds Lean could not rule out; when empty,
    the transformation provably runs without them."""

    @property
    def proved(self) -> bool:
        """Every postcondition holds and no runtime error is possible."""
        return all(c.proved for c in self.ensures) and not self.errors

    @property
    def errors(self) -> list[Issue]:
        return [i for i in self.issues if i.error]

    @property
    def warnings(self) -> list[Issue]:
        return [i for i in self.issues if not i.error]

    @property
    def unproved(self) -> list[CheckedCondition]:
        return [c for c in self.ensures if not c.proved]

    def __str__(self) -> str:
        lines = []
        for table, conds in self.requires.items():
            lines += [f"requires {table}: {c}" for c in conds]
        for c in self.ensures:
            mark = "proved" if c.proved else f"NOT proved (it is {c.value})"
            lines.append(f"ensures {c.label}: {mark}")
        lines += [f"may fail: {i}" for i in self.errors]
        lines += [f"warning: {i}" for i in self.warnings]
        if not self.deterministic:
            lines.append(f"note: {TIES_HINT}")
        if self.facts:
            lines.append("known about the output:")
            lines += [f"  {name}: {value}" for name, value in self.facts.items()]
        return "\n".join(lines)

    def _repr_markdown_(self) -> str:
        rows = [
            f"| `{c.label}` | {'✅ proved' if c.proved else '❌ ' + c.value} |"
            for c in self.ensures
        ]
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
    """A postcondition, or the absence of runtime errors, could not be proved."""

    def __init__(self, report: Report):
        self.report = report
        problems = [f"{c.label} (it is {c.value})" for c in report.unproved]
        problems += [f"no runtime error ({i})" for i in report.errors]
        super().__init__(f"could not prove: {', '.join(problems)}\n{report}")


class PreconditionError(Exception):
    """Input data violates a precondition."""


class PostconditionError(Exception):
    """Output data violates a postcondition (only raised by runtime checks)."""


# Doubles, timestamps and dates are integer codes in the Lean model
# (SubstraitLean/Float.lean). A double with magnitude m = |x| * 2^1074 has
# code ±(2m + 1), which orders codes like DataFusion orders doubles
# (-NaN < -inf < ... < -0.0 < +0.0 < ... < +inf < NaN). Timestamps are
# microseconds, dates days.
MAX_MAG = (2**53 - 1) * 2**2045
INF_MAG, NAN_MAG = MAX_MAG + 1, MAX_MAG + 2


def decode_double(code: int) -> float:
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
            # Valid codes are odd; an even bound lies strictly between two doubles.
            def ge(k: int) -> str:
                return f"≥ {show(k)}" if k % 2 else f"> {show(k - 1)}"

            def le(k: int) -> str:
                return f"≤ {show(k)}" if k % 2 else f"< {show(k + 1)}"

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
) -> Report:
    """Try to prove `ensures` about `transform` (an Ibis table expression or a
    SQL query) from `requires`, a mapping from table name to conditions.

    `tables` gives the input schemas; it is only needed for SQL transforms.
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

    req_plans = [
        plan(condition_query(table_ref(t), c))
        for t, cs in requires.items()
        for c in cs
        if not isinstance(c, Unique)
    ]
    ens_plans = []
    for c in ensures:
        if isinstance(c, Unique):
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
    contract = {
        "requires": req_plans,
        "ensures": ens_plans,
        "transform": transform_plan,
        "keys": keys,
        "ensures_keys": ensures_keys,
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
            checked.append(CheckedCondition(label(c), ok, value))
        else:
            e = next(rows)
            checked.append(CheckedCondition(e["name"], e["proved"], e["value"]))
    return Report(
        requires={t: [label(c) for c in cs] for t, cs in requires.items()},
        ensures=checked,
        facts={f["name"]: describe(f) for f in out["facts"]},
        deterministic=out["deterministic"],
        issues=[Issue(i["kind"], i["expr"], i["error"]) for i in out["issues"]],
    )


def violations(table: ir.Table, cond: Condition, engine: Engine | None = None) -> int:
    """Rows of a bound table where `cond` is not TRUE (FALSE or NULL), or for
    `unique`, rows beyond the first for each repeated key.

    With an engine named, the condition's plan runs there, over the tables of
    the connection `table` is bound to; otherwise Ibis counts on that
    connection."""
    if not isinstance(cond, Unique) and engine is not None:
        con = connection_of(table)
        if con is None:
            raise ValueError("checking a condition on an engine needs a table of sverify.connect()")
        plan = written_plan(plan_json(con, condition_query(table, cond)))
        return sum(v is not True for v in run_plan(con, plan, engine).column(0).to_pylist())
    if isinstance(cond, Unique):
        total: Any = table.count()
        distinct: Any = table.select(*cond.cols).distinct().count()
        return int(total.execute()) - int(distinct.execute())
    if isinstance(cond, str):
        backend: Any = ibis.get_backend(table)
        sql = ibis.to_sql(table, dialect=backend.name)
        return (
            backend.sql(f'SELECT * FROM ({sql}) AS "t" WHERE NOT coalesce(({cond}), FALSE)')
            .count()
            .execute()
        )
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
            report = verify(table, requires={name: list(facts)}, ensures=conds)
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
            rowwise = [c for c in todo if not isinstance(c, Unique)]
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
    by what the contracted transformation producing that input guarantees."""

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
    """A transformation with a contract; see `transform`."""

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

    def __call__(self, *args, **kwargs) -> ir.Table:
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
    """
    return lambda fn: ContractedTransform(
        fn, requires or {}, ensures, on_unproved, check_requires, engine
    )
