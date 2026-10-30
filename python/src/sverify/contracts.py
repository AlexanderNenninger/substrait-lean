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

Conditions are Ibis expressions (`_.amount >= 0`, or a function of the table)
or SQL snippets (`"amount >= 0"`). DataFusion compiles them to Substrait.
"""

from __future__ import annotations

import functools
import inspect
import json
import math
import subprocess
import tempfile
import warnings
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta
from fractions import Fraction
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.deferred import Deferred

from sverify.engine import connect, create_table, substrait_json, to_sql
from sverify.incremental import checker_path


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
    or "may wrap around" (64-bit overflow of `+`, `-`, `*`, which DataFusion
    does not report)."""
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
        rows += [f"| runtime | ❌ may fail: {i} |" for i in self.errors]
        rows += [f"| runtime | ⚠️ {i} |" for i in self.warnings]
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


def condition_sql(table: Transform, cond: Condition) -> str:
    """SQL selecting one condition column from a table or transformation."""
    if isinstance(cond, str):
        source = table if isinstance(table, str) else to_sql(table)
        return f'SELECT ({cond}) AS "c" FROM ({source}) AS "t"'
    if isinstance(table, str):
        raise TypeError("Ibis conditions need an Ibis transformation; use a SQL string instead")
    return to_sql(table.select(c=resolve(cond, table)))


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

    def plan(sql: str) -> Any:
        return json.loads(substrait_json(con, sql))

    def table_ref(name: str) -> Transform:
        return f"SELECT * FROM {q(name)}" if isinstance(transform, str) else con.table(name)

    req_plans = [
        plan(condition_sql(table_ref(t), c))
        for t, cs in requires.items()
        for c in cs
        if not isinstance(c, Unique)
    ]
    ens_plans = []
    for c in ensures:
        if isinstance(c, Unique):
            continue
        p = plan(condition_sql(transform, c))
        p["relations"][0]["root"]["names"] = [label(c)]
        ens_plans.append(p)
    transform_sql = transform if isinstance(transform, str) else to_sql(transform)
    transform_plan = plan(transform_sql)
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

    with tempfile.NamedTemporaryFile("w", suffix=".json") as f:
        json.dump(contract, f)
        f.flush()
        proc = subprocess.run(
            [str(checker_path()), "--contract", f.name], capture_output=True, text=True
        )
    if proc.returncode not in (0, 4):
        raise ValueError(f"substrait-check --contract failed: {proc.stderr.strip()}")
    out = json.loads(proc.stdout)
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


def violations(table: ir.Table, cond: Condition) -> int:
    """Rows of a backend-bound table where `cond` is not TRUE (FALSE or NULL),
    or for `unique`, rows beyond the first for each repeated key."""
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


def is_bound(table: ir.Table) -> bool:
    try:
        ibis.get_backend(table)
    except Exception:
        return False
    return True


class ContractedTransform:
    """A transformation with a contract; see `transform`."""

    def __init__(
        self,
        fn: Callable[..., ir.Table],
        requires: Mapping[str, Sequence[Condition]],
        ensures: Sequence[Condition],
        on_unproved: Literal["error", "runtime", "warn"],
        check_requires: bool,
    ):
        self.fn, self.requires, self.ensures = fn, requires, ensures
        self.on_unproved, self.check_requires = on_unproved, check_requires
        self.signature = inspect.signature(fn)
        unknown = set(requires) - set(self.signature.parameters)
        if unknown:
            raise TypeError(f"requires names unknown parameters: {sorted(unknown)}")
        self.last_report: Report | None = None
        self._cache: dict[tuple, Report] = {}
        functools.update_wrapper(self, fn)

    def __call__(self, *args, **kwargs) -> ir.Table:
        inputs = self.signature.bind(*args, **kwargs).arguments
        result = self.fn(*args, **kwargs)
        if self.check_requires:
            for param, conds in self.requires.items():
                table = inputs[param]
                if is_bound(table):
                    for c in conds:
                        if n := violations(table, c):
                            raise PreconditionError(f"{n} row(s) of {param} violate {label(c)}")
        key = tuple((p, inputs[p].get_name(), inputs[p].schema()) for p in self.requires) + (
            to_sql(result),
        )
        if key not in self._cache:
            self._cache[key] = verify(
                result,
                requires={inputs[p].get_name(): cs for p, cs in self.requires.items()},
                ensures=self.ensures,
            )
        report = self.last_report = self._cache[key]
        if not report.proved:
            if self.on_unproved == "warn":
                warnings.warn(str(VerificationError(report)), stacklevel=2)
            # Runtime errors cannot be checked on the data beforehand: in
            # "runtime" mode the engine raises them if they happen.
            elif self.on_unproved == "runtime" and is_bound(result):
                unproved = {c.label for c in report.unproved}
                for c in self.ensures:
                    if label(c) in unproved and (n := violations(result, c)):
                        raise PostconditionError(f"{n} output row(s) violate {label(c)}")
            else:
                raise VerificationError(report)
        return result


def transform(
    requires: Mapping[str, Sequence[Condition]] | None = None,
    ensures: Sequence[Condition] = (),
    *,
    on_unproved: Literal["error", "runtime", "warn"] = "error",
    check_requires: bool = True,
) -> Callable[[Callable[..., ir.Table]], ContractedTransform]:
    """Decorate a function from Ibis tables to an Ibis table with a contract.

    `requires` maps parameter names to conditions on that input. On each call
    the postconditions are proved (cached per input schema and expression) and
    the report is kept in `.last_report`; see the module docstring. With
    `on_unproved="runtime"`, unproved postconditions are checked on the output
    data instead, which needs inputs bound to a backend.
    """
    return lambda fn: ContractedTransform(fn, requires or {}, ensures, on_unproved, check_requires)
