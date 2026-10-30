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
or SQL snippets (`"amount >= 0"`). DuckDB only compiles them to Substrait here;
the transformation itself can run on any Ibis backend.
"""

from __future__ import annotations

import functools
import inspect
import json
import subprocess
import tempfile
import warnings
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.deferred import Deferred

from sverify.duck import connect, substrait_json
from sverify.incremental import checker_path, q

Condition = Deferred | ir.BooleanValue | str | Callable[[ir.Table], ir.BooleanValue]
Transform = ir.Table | str


@dataclass
class CheckedCondition:
    label: str
    proved: bool
    value: str
    """What Lean established about the condition, e.g. "TRUE or NULL"."""


@dataclass
class Report:
    requires: dict[str, list[str]]
    ensures: list[CheckedCondition]
    facts: dict[str, str] = field(default_factory=dict)
    """What Lean established about each output column."""

    @property
    def proved(self) -> bool:
        return all(c.proved for c in self.ensures)

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
        if self.facts:
            lines.append("known about the output:")
            lines += [f"  {name}: {value}" for name, value in self.facts.items()]
        return "\n".join(lines)

    def _repr_markdown_(self) -> str:
        rows = [
            f"| `{c.label}` | {'✅ proved' if c.proved else '❌ ' + c.value} |"
            for c in self.ensures
        ]
        facts = [f"| `{n}` | {v} |" for n, v in self.facts.items()]
        return "\n".join(
            [
                "| postcondition | status |",
                "|---|---|",
                *rows,
                "",
                "| output column | known values |",
                "|---|---|",
                *facts,
            ]
        )


class VerificationError(Exception):
    """A postcondition could not be proved."""

    def __init__(self, report: Report):
        self.report = report
        unproved = ", ".join(f"{c.label} (it is {c.value})" for c in report.unproved)
        super().__init__(f"could not prove: {unproved}\n{report}")


class PreconditionError(Exception):
    """Input data violates a precondition."""


class PostconditionError(Exception):
    """Output data violates a postcondition (only raised by runtime checks)."""


def label(cond: Condition) -> str:
    if isinstance(cond, str):
        return cond
    if isinstance(cond, Deferred):
        return repr(cond)
    return getattr(cond, "__name__", repr(cond))


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
        source = table if isinstance(table, str) else ibis.to_sql(table, dialect="duckdb")
        return f'SELECT ({cond}) AS "c" FROM ({source}) AS "t"'
    if isinstance(table, str):
        raise TypeError("Ibis conditions need an Ibis transformation; use a SQL string instead")
    return ibis.to_sql(table.select(c=resolve(cond, table)), dialect="duckdb")


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
    db = ibis.duckdb.from_connection(con)
    for name, schema in schemas.items():
        db.create_table(name, schema=schema)

    def plan(sql: str) -> Any:
        return json.loads(substrait_json(con, sql))

    def table_ref(name: str) -> Transform:
        return f"SELECT * FROM {q(name)}" if isinstance(transform, str) else db.table(name)

    req_plans = [plan(condition_sql(table_ref(t), c)) for t, cs in requires.items() for c in cs]
    ens_plans = []
    for c in ensures:
        p = plan(condition_sql(transform, c))
        p["relations"][0]["root"]["names"] = [label(c)]
        ens_plans.append(p)
    transform_sql = transform if isinstance(transform, str) else ibis.to_sql(transform, "duckdb")
    contract = {"requires": req_plans, "ensures": ens_plans, "transform": plan(transform_sql)}

    with tempfile.NamedTemporaryFile("w", suffix=".json") as f:
        json.dump(contract, f)
        f.flush()
        proc = subprocess.run(
            [str(checker_path()), "--contract", f.name], capture_output=True, text=True
        )
    if proc.returncode not in (0, 4):
        raise ValueError(f"substrait-check --contract failed: {proc.stderr.strip()}")
    out = json.loads(proc.stdout)
    return Report(
        requires={t: [label(c) for c in cs] for t, cs in requires.items()},
        ensures=[CheckedCondition(e["name"], e["proved"], e["value"]) for e in out["ensures"]],
        facts={f["name"]: f["value"] for f in out["facts"]},
    )


def violations(table: ir.Table, cond: Condition) -> int:
    """Rows of a backend-bound table where `cond` is not TRUE (FALSE or NULL)."""
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
            ibis.to_sql(result, dialect="duckdb"),
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
