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
postcondition raises `VerificationError` that says what the checker could establish,
unless `on_unproved` asks for a runtime check or a warning instead.

Preconditions are assumptions about data that comes from outside, so when the
inputs are bound to a backend they are checked on the data at call time.

Contracted transformations compose. When the result of one feeds another, the
downstream precondition is *proved* from the upstream contract instead of
checked on the data, and the downstream postconditions are proved assuming
only what the upstream one guarantees (`Triple.compose` in
`SubstraitLean/Compose.lean`):

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    doubled(paid(orders))     # `doubled` is proved from `paid`'s guarantees

A link that does not hold raises `CompositionError` naming both sides:
"doubled needs (_.amount >= 0) (it may be FALSE on some rows) on 't'; not_null only
guarantees _.amount.notnull()". Plain Ibis steps in between carry no
guarantees of their own. A composed result can be maintained incrementally
(`sverify.incremental`): its preconditions on the base tables are then
checked on each batch of changes, and its guarantees hold in every state.

Conditions are Ibis expressions (`_.amount >= 0`, or a function of the table)
or SQL snippets (`"amount >= 0"`). SQL snippets are DuckDB's SQL, compiled to
Substrait by sverify's lift (`sverify.sql_lift`).

Runtime checks run through Ibis, on the connection the tables are bound to
(`sverify.connect()`), by default; naming an engine (`engine="duckdb"`,
or `"polars"`, see `sverify.engines.run`) runs each
condition's plan, as Lean wrote it, there instead, so such conditions must be
inside the Lean model. `unique` checks always run through Ibis.
"""

from __future__ import annotations

import difflib
import functools
import inspect
import json
import math
import os
import re
import warnings
import weakref
from collections.abc import Callable, Collection, Container, Mapping, Sequence
from dataclasses import dataclass, field, replace
from datetime import date, datetime, timedelta
from decimal import Decimal
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.deferred import Deferred
from ibis.common.graph import Node

from sverify import _hooks, _pipe, _stages
from sverify import observation as _observation
from sverify._checker import INF_MAG, MAX_MAG, NAN_MAG, decode_double  # noqa: F401
from sverify._hooks import COLLECTING, Collected
from sverify._quarantine import Policy, check_policy
from sverify._unsupported import SverifyWarning
from sverify.conditions import (  # noqa: F401  (re-exported: `sverify.contracts` keeps its names)
    _DATA_ONLY,
    DATA_CHECK,
    ON_DATA,
    ROWS_SHOWN,
    Approx,
    ArrivesWithin,
    CheckedCondition,
    Discharged,
    Inferred,
    Key,
    MaxRows,
    PreconditionError,
    References,
    RelationRows,
    RowsPer,
    TableCondition,
    Unique,
    _check_approx,
    _count,
    _duplicate_rows,
    _KeyResult,
    _positions,
    _relax,
    _Rows,
    approx,
    arrives_within,
    expand_keys,
    label,
    max_rows,
    q,
    references,
    resolve,
    rows_per,
    show_duration,
    unique,
)
from sverify.counterexample import Counterexample
from sverify.counterexample import search as search_counterexample
from sverify.engine import (
    Connection,
    Engine,
    checker_failed,
    connect,
    plan_json,
    run_checker,
)
from sverify.observation import Observation, _deterministic_arg  # noqa: F401  (re-exported)
from sverify.report import (  # noqa: F401  (re-exported: `sverify.contracts` keeps its names)
    _DECIMAL_ARG,
    _EPOCH_DAY,
    _MICROSECOND,
    _ORDERED,
    _REPORT_INTERNAL,
    CONSTANT_HINT,
    FINITE_ASSUMED,
    INFINITE,
    INFINITE_HINT,
    OVERFLOW_HINT,
    PARAMS_NOTE,
    RUNTIME_CHECK,
    SUM_ASSUMED,
    TIES_HINT,
    TRUNC_HINT,
    Condition,
    Issue,
    Needed,
    OnInferred,
    PostconditionError,
    Report,
    Semantics,
    TiePlace,
    Transform,
    UnprovedReason,
    UnverifiedRunError,
    VerificationError,
    _assumable,
    _assumption,
    _cause,
    _labels_by_table,
    _needed,
    _needed_deferred,
    _sql_value,
    _sum,
    _sum_assumed,
    _transfer_failure,
    _truncates,
    _unparen,
    _would_hold,
    condition_query,
    error_text,
    render_fact,
    tie_places,
    violating_rows,
    violations,
)

type Policies = dict[str, dict[str, set[Policy | None]]]
"""By table and condition label, the `on_violation` of each transform that
states the condition (None: unset)."""


#: The profiles the checker is asked for by name (`"profile"` in a
#: `--contract` request): those beyond the reference and DuckDB's lift.
_PROFILE_REQUESTS = frozenset({"polars", "spark", "substrait"})


def _expr_semantics(transform: Transform) -> Semantics:
    """The semantics an unstated `verify(semantics=...)` takes: an expression
    whose SQL (`sverify.sql`) is all lifted with DuckDB's semantics has
    them (#575: so its report assumes no ±∞ precondition and `Report.run`
    writes no check of one); anything else, the reference."""
    if isinstance(transform, str):
        return "reference"
    from sverify.ibis_substrait.relations import SQLModel

    found = transform.op().find(SQLModel)
    sems = {op.semantics or "reference" for op in found}
    return "duckdb" if sems == {"duckdb"} else "reference"


def _profile_requests() -> frozenset[str]:
    """`_PROFILE_REQUESTS`, with the installed profiles from outside sverify
    (`sverify.profiles`)."""
    from sverify import profiles

    return _PROFILE_REQUESTS | frozenset(profiles.plugins())


def _checked_semantics(semantics: str) -> Semantics:
    from sverify import profiles

    if semantics in profiles.plugins():
        return semantics  # type: ignore[return-value]
    if semantics not in ("reference", "duckdb", "polars", "spark", "substrait"):
        raise ValueError(
            "semantics must be 'reference', 'duckdb', 'polars', 'spark', 'substrait' or an "
            "installed engine profile (sverify.profiles), "
            f"not {semantics!r}"
        )
    return semantics  # type: ignore[return-value]


def _warning_text(error: VerificationError) -> str:
    """An `UnprovedWarning`'s message: the error's, where the warning's
    `.report` has the details."""
    return str(error).replace("(e.report has the details)", "(.report has the details)", 1)


def _code_literal(dtype: Any, code: int) -> str | None:
    """The SQL literal of a value Lean codes as the integer `code`, for the
    types whose order is the order of their codes: integers, dates (days)
    and timestamps without a time zone (microseconds). None for the rest."""
    try:
        if dtype.is_integer():
            return str(code)
        if dtype.is_date():
            return f"DATE '{(_EPOCH + timedelta(days=code)).date().isoformat()}'"
        if dtype.is_timestamp() and dtype.timezone is None and dtype.scale in (None, 6):
            ts = _EPOCH + timedelta(microseconds=code)
            return f"TIMESTAMP '{ts.isoformat(sep=' ', timespec='microseconds')}'"
    except OverflowError:
        return None
    return None


_INT64_ENDS = (-(2**63), 2**63 - 1)


def _implied_sql(raw: Sequence[dict], schemas: Mapping[str, Any]) -> dict[str, str]:
    """The implied predicates of Lean's report as SQL, per table: the
    disjunction of each abstract row's column bounds. A bound on a type
    without an order-preserving literal is left out, which only weakens the
    condition; a table where some abstract row keeps no bound gets none."""
    out: dict[str, str] = {}
    for entry in raw:
        schema = schemas.get(entry["table"])
        if schema is None:
            continue
        names = list(schema.names)
        disjuncts = []
        for bounds in entry["any"]:
            conj = []
            for b in bounds:
                col = names[b["col"]]
                ref = '"' + col.replace('"', '""') + '"'
                for op, v in ((">=", b["lo"]), ("<=", b["hi"])):
                    if v is None or (schema[col].is_integer() and int(v) in _INT64_ENDS):
                        continue  # no bound, or only the type's own range
                    lit = _code_literal(schema[col], int(v))
                    if lit is not None:
                        conj.append(f"{ref} {op} {lit}")
            if not conj:
                break
            disjuncts.append(" AND ".join(conj))
        else:
            if disjuncts:
                out[entry["table"]] = " OR ".join(f"({d})" for d in disjuncts)
    return out


def _nice(x: int, up: bool) -> tuple[int, str]:
    """A round number near `x`, at or above it if `up`, else at or below,
    and how to write it: `2**62`, `3 * 10**18` or `1_000`."""
    if x < 0:
        v, text = _nice(-x, not up)
        return -v, f"-{text}" if v else "0"
    if x < 10**6:
        return x, f"{x:_}"
    k = x.bit_length() - 1
    two = 2 ** (k + 1 if up and 2**k < x else k)
    e = len(str(x)) - 1
    d = x // 10**e + (1 if up and x % 10**e else 0)
    ten = d * 10**e
    better = min if up else max
    v = better(two, ten)
    if v == two:
        return v, f"2**{v.bit_length() - 1}"
    d, e = (v // 10**e, e) if v // 10**e < 10 else (1, e + 1)
    return v, (f"10**{e}" if d == 1 else f"{d} * 10**{e}")


_EPOCH = datetime(1970, 1, 1)


_US_MIN = (datetime.min - _EPOCH) // timedelta(microseconds=1)


_US_MAX = (datetime.max - _EPOCH) // timedelta(microseconds=1)


def _year_of(code: int, per_year_unit: timedelta) -> int:
    """The year of a timestamp (microseconds) or date (days) code, clamped to
    Python's years."""
    us = code * (per_year_unit // timedelta(microseconds=1))
    if us < _US_MIN:
        return 1
    if us > _US_MAX:
        return 9999
    return (_EPOCH + timedelta(microseconds=us)).year


def _bound_conditions(col: str, dtype: Any, lo: int | None, hi: int | None) -> list[Inferred]:
    """`lo <= col <= hi` as conditions, rounded inward to round numbers (or
    whole years), each side its own condition. Empty for a type the
    inference does not write bounds for."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    # NULL cannot overflow, so a bound lets it pass.
    null = f"{sql} IS NULL OR " if dtype.nullable else ""
    out = []
    if dtype.is_integer():
        # A side at or past 64 bits holds for every integer column, and its
        # constant (2**63) would be a HUGEINT, which the lift refuses (#616).
        # A narrower column's own limits stay, the proof needs them stated,
        # each a constant of the column's type, so it is a fact about the
        # column (`v <= 127` on a TINYINT, not `v < 128`).
        if lo is not None and lo <= -(2**63):
            lo = None
        if hi is not None and hi >= 2**63 - 1:
            hi = None
        if lo is not None:
            if lo <= dtype.bounds.lower:
                v, text = dtype.bounds.lower, f"{dtype.bounds.lower:_}"
            else:
                v, text = _nice(lo, up=True)
            out.append(Inferred(f"{null}{sql} >= {v}", f"({ref} >= {text})"))
        if hi is not None:
            if hi >= dtype.bounds.upper:
                top = dtype.bounds.upper
                out.append(Inferred(f"{null}{sql} <= {top}", f"({ref} <= {top:_})"))
            else:
                v, text = _nice(hi + 1, up=False)
                out.append(Inferred(f"{null}{sql} < {v}", f"({ref} < {text})"))
        return out
    if dtype.is_floating():
        return _double_conditions(ref, sql, null, lo, hi)
    if dtype.is_decimal() and dtype.scale is not None:
        scale = dtype.scale

        def dec(k: int) -> str:
            return f"{Decimal(k).scaleb(-scale):.{scale}f}"

        # Large bounds as round whole numbers (`5 * 10**35`), small ones exactly.
        if lo is not None:
            if abs(lo) >= 10 ** (scale + 6):
                v, text = _nice(-((-lo) // 10**scale), up=True)
                out.append(Inferred(f"{null}{sql} >= {dec(v * 10**scale)}", f"({ref} >= {text})"))
            else:
                out.append(Inferred(f"{null}{sql} >= {dec(lo)}", f"({ref} >= {dec(lo)})"))
        if hi is not None:
            if abs(hi) >= 10 ** (scale + 6):
                v, text = _nice(hi // 10**scale + 1, up=False)
                out.append(Inferred(f"{null}{sql} < {dec(v * 10**scale)}", f"({ref} < {text})"))
            else:
                out.append(Inferred(f"{null}{sql} <= {dec(hi)}", f"({ref} <= {dec(hi)})"))
        return out
    if dtype.is_timestamp() and dtype.timezone is None:
        unit, kind, py = timedelta(microseconds=1), "TIMESTAMP", "datetime"
    elif dtype.is_date():
        unit, kind, py = timedelta(days=1), "DATE", "date"
    else:
        return []

    def code(year: int) -> int:
        return (datetime(year, 1, 1) - _EPOCH) // unit

    def lit(year: int) -> str:
        day = date(year, 1, 1)
        return f"{kind} '{day.isoformat()}{' 00:00:00' if kind == 'TIMESTAMP' else ''}'"

    if lo is not None:
        y = _year_of(lo, unit)
        if code(y) < lo:
            y += 1
        out.append(Inferred(f"{null}{sql} >= {lit(y)}", f"({ref} >= {py}({y}, 1, 1))"))
    if hi is not None:
        y = _year_of(hi + 1, unit)
        out.append(Inferred(f"{null}{sql} < {lit(y)}", f"({ref} < {py}({y}, 1, 1))"))
    return out


# Codes of the smallest positive and the largest finite double.
_TINY_CODE = 1


_MAX_CODE = 2 * MAX_MAG + 1


def _double_conditions(
    ref: str, sql: str, null: str, lo: int | None, hi: int | None
) -> list[Inferred]:
    """`lo <= col <= hi` on double codes: `> 0` for the smallest positive
    double, round powers of two near ±2⁶³ (a cast to BIGINT), and the
    decoded doubles otherwise."""

    def num(x: float) -> str:
        if x.is_integer() and abs(x) >= 1e6:
            return _nice(int(x), up=x < 0)[1]
        return repr(x)

    out = []
    if lo is not None:
        if lo == _TINY_CODE:
            out.append(Inferred(f"{null}{sql} > 0", f"({ref} > 0)"))
        elif lo > -_MAX_CODE:
            x = decode_double(lo)
            out.append(Inferred(f"{null}{sql} >= {x!r}", f"({ref} >= {num(x)})"))
        else:
            x = decode_double(-_MAX_CODE)
            out.append(Inferred(f"{null}{sql} >= {x!r}", f"({ref} >= {x!r})"))
    if hi is not None:
        nxt = decode_double(hi + 1)
        if hi < _MAX_CODE and nxt.is_integer() and abs(nxt) >= 1e6:
            # Just below a round number: `< 2**63`.
            out.append(Inferred(f"{null}{sql} < {nxt!r}", f"({ref} < {num(nxt)})"))
        else:
            x = decode_double(min(hi, _MAX_CODE))
            out.append(Inferred(f"{null}{sql} <= {x!r}", f"({ref} <= {x!r})"))
    return out


def _ne_condition(col: str, dtype: Any, k: int) -> Inferred | None:
    """`col != k`, for a code `k` of the column's type (a divisor's 0)."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    null = f"{sql} IS NULL OR " if dtype.nullable else ""
    if dtype.is_integer():
        v = str(k)
    elif dtype.is_floating():
        v = repr(decode_double(k))
    elif dtype.is_decimal() and dtype.scale is not None:
        v = f"{Decimal(k).scaleb(-dtype.scale):.{dtype.scale}f}"
    else:
        return None
    return Inferred(f"{null}{sql} <> {v}", f"({ref} != {v})")


def _not_null_condition(col: str) -> Inferred:
    """`col IS NOT NULL` (a divisor's `COUNT` of the column)."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    return Inferred(f"{sql} IS NOT NULL", f"{ref}.notnull()")


def _suggested(
    bound: dict | None, schemas: Mapping[str, ibis.Schema], assumable: Container[str]
) -> dict[str, list[Condition]]:
    """The preconditions Lean suggests for an unproved postcondition, on the
    tables whose `requires` the caller states; none for a split or a why."""
    if bound is None or bound["why"] is not None or bound["split"]:
        return {}
    conds = _render_needs(bound["needs"], schemas)
    return {t: list[Condition](cs) for t, cs in conds.items() if t in assumable and cs}


def _render_needs(
    needs: Sequence[dict], schemas: Mapping[str, ibis.Schema]
) -> dict[str, list[Inferred]]:
    """The conditions of a list of `{table, col, lo, hi}`, `{table, col,
    ne}` or `{table, col, not_null}` (column positions, integer codes as
    strings), per table."""
    out: dict[str, list[Inferred]] = {}
    for n in needs:
        schema = schemas.get(n["table"])
        if schema is None or n["col"] >= len(schema):
            continue
        col = list(schema)[n["col"]]
        have = out.setdefault(n["table"], [])
        if n.get("not_null"):
            new = [_not_null_condition(col)] if schema[col].nullable else []
        elif "ne" in n:
            c = _ne_condition(col, schema[col], int(n["ne"]))
            new = [] if c is None else [c]
        else:
            lo, hi = (None if n[k] is None else int(n[k]) for k in ("lo", "hi"))
            new = _bound_conditions(col, schema[col], lo, hi)
        for c in new:
            c.column = col
        have += [c for c in new if c not in have]
    return {t: cs for t, cs in out.items() if cs}


def _why_hint(why: str, show: Callable[[str], str]) -> str:
    """Why no bound on an input column rules an issue out, from the
    inference's reason (`SubstraitLean/Infer.lean`), in the user's terms."""
    m = re.fullmatch(r"it divides by (.+), which the inference does not look into", why)
    if m and re.fullmatch(r"-?0(\.0*)?d?", m[1]):
        return "it divides by the constant 0, so every row it reaches raises: change the divisor"
    m = re.fullmatch(r"(it divides by|it reads|its base is) (.+)(, which .*)", why)
    if m:
        why = f"{m[1]} `{show(m[2])}`{m[3]}"
    return f"sverify found no bound on an input column that rules it out: {why}"


def _hint(
    bound: dict | None,
    schemas: Mapping[str, ibis.Schema],
    assumable: Container[str],
    show: Callable[[str], str] = lambda e: e,
) -> str | None:
    """What a report suggests for one overflow, from what the inference
    found (`SubstraitLean/Infer.lean`)."""
    if bound is None:
        return None
    if bound["why"] is not None:
        return _why_hint(bound["why"], show)
    conds = _render_needs(bound["needs"], schemas)
    if not conds:
        return None

    def code(cs: Sequence[Inferred]) -> str:
        return ", ".join(f"`{label(c)}`" for c in cs)

    parts = []
    for t, cs in conds.items():
        if t in assumable:
            parts.append(f"{code(cs)} in the requires of {t!r}")
        else:
            parts.append(f"{code(cs)} in the ensures of {t!r}")
    lead = "no single bound rules it out; for example, state " if bound["split"] else "state "
    return lead + " and ".join(parts)


def column_names(schema: ibis.Schema) -> list[str]:
    return [name for name, _ in schema.items()]


def leaf_tables(expr: ir.Table) -> dict[str, ibis.Schema]:
    leaves = expr.op().find((ops.UnboundTable, ops.DatabaseTable))
    return {t.name: t.schema for t in leaves if isinstance(t, ops.UnboundTable | ops.DatabaseTable)}


def bind_params(expr: ir.Table, params: Mapping[ir.Scalar, Any]) -> ir.Table:
    """`expr` with each `ibis.param` in `params` replaced by its value, a
    literal of the parameter's type (#58), as Ibis's `execute(params=...)`
    binds them.

    Raises:
        TypeError: A key is not an `ibis.param`, or a value does not fit its
            type.
    """
    mapping: dict[Any, Any] = {}
    for p, value in params.items():
        op = p.op() if isinstance(p, ir.Expr) else None
        if not isinstance(op, ops.ScalarParameter):
            raise TypeError(f"params keys must be ibis.param expressions, not {p!r}")
        try:
            lit = ibis.literal(value, type=op.dtype)
        except Exception as e:  # noqa: BLE001 - Ibis raises several kinds
            raise TypeError(f"{value!r} is not a value of the parameter's type {op.dtype}") from e
        mapping[op] = lit.op()
    return expr.op().replace(mapping).to_expr()


def requires_by_input(
    requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None,
    inputs: Sequence[str],
    kind: str = "table",
    error: type[Exception] = ValueError,
) -> dict[str, Sequence[Condition]]:
    """`requires` as a mapping from input to its conditions (#408). A plain
    list is the conditions on the only input; a key that names no input
    raises `error`, naming the key, the inputs and a close match."""
    if requires is None:
        return {}
    if not isinstance(requires, Mapping):
        conds: list[Any] = (
            [requires] if isinstance(requires, str | TableCondition | Key) else list(requires)
        )
        if len(inputs) != 1:
            raise error(
                f"requires: a list of conditions needs exactly one input {kind}, and there "
                f"are {len(inputs)} ({', '.join(inputs) or 'none'}); key them by {kind}, "
                "as requires={name: [...]}"
            )
        return {inputs[0]: expand_keys(conds)}
    for key in requires:
        if key in inputs:
            continue
        lower = {i.lower(): i for i in inputs}
        close = [lower[k] for k in difflib.get_close_matches(str(key).lower(), lower, n=1)]
        hint = f"; did you mean {close[0]!r}?" if close else ""
        raise error(
            f"requires: unknown {kind} {key!r}; the inputs are: {', '.join(inputs) or 'none'}"
            + hint
        )
    return {t: expand_keys(cs) for t, cs in requires.items()}


def default_counterexamples() -> int:
    """How many inputs `verify`, a transform's call and
    `ContractedTransform.check` try per unproved postcondition when not told:
    the `SVERIFY_COUNTEREXAMPLES` environment variable, else 200. An editor
    or a CI step that only needs the verdicts sets it to 0."""
    raw = os.environ.get("SVERIFY_COUNTEREXAMPLES", "").strip()
    if not raw:
        return 200
    try:
        n = int(raw)
    except ValueError:
        raise ValueError(f"SVERIFY_COUNTEREXAMPLES must be an integer, not {raw!r}") from None
    if n < 0:
        raise ValueError(f"SVERIFY_COUNTEREXAMPLES must be 0 or more, not {n}")
    return n


def verify(
    query: Transform,
    /,
    *,
    requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None = None,
    ensures: Sequence[Condition] = (),
    tables: Mapping[str, ibis.Schema | ir.Table] | None = None,
    counterexamples: int | None = None,
    params: Mapping[ir.Scalar, Any] | None = None,
    semantics: Semantics | None = None,
    on_inferred: OnInferred = "error",
) -> Report:
    """Try to prove `ensures` about `query` (an Ibis table expression or a
    SQL query) from `requires`, a mapping from table name to conditions.

    `tables` gives the input schemas; it is only needed for SQL transforms.
    For each unproved postcondition, up to `counterexamples` small inputs are
    tried for one that breaks it (`sverify.counterexample`); 0 skips that.

    A proof is about the plan `transform` compiles to, under `Rel.eval`. An
    Ibis expression compiles with sverify's own producer, so it means what
    `docs/reference-semantics.md` ("The Ibis frontend") says, whichever Ibis
    backend it came from; where
    Ibis backends disagree (`%` on Polars, `-0.0 == 0.0` on DataFusion, …),
    no backend's `execute` is guaranteed to match. `sverify.engines.run`
    runs the verified plan with that meaning (or fails) on DuckDB and
    Polars. A SQL string, and a SQL condition, is DuckDB's SQL, lifted by
    `sverify.sql_lift` with `semantics`: the reference semantics by default,
    or what DuckDB computes with `semantics="duckdb"` (#411). The report
    says which (`Report.semantics`).

    Unlike `transform`, `verify` checks nothing on data and raises nothing
    when a postcondition is unproved: it returns the report.

    Args:
        transform: The transformation, as an Ibis table expression or a SQL
            query.
        requires: Preconditions, as a mapping from input table name to its
            conditions (Ibis expressions, SQL snippets, `unique` or
            `references`), or, for a transformation with one input, a list
            of its conditions. They are assumed, not checked. Default: none.
        ensures: Postconditions on the output to prove, including `unique`
            keys. Default: none, which still reports the facts and possible
            runtime errors.
        tables: Input schemas by table name, as Ibis schemas, anything
            `ibis.schema` accepts, Ibis tables, or mappings of column names
            to DuckDB's type names (`{"id": "BIGINT", "name": "VARCHAR NOT
            NULL"}`, `input_schema`). Needed for SQL transforms; an Ibis
            expression's own tables are found from it.
        counterexamples: How many small inputs to try per unproved
            postcondition when searching for one that breaks it; 0 skips the
            search. Default: the `SVERIFY_COUNTEREXAMPLES` environment
            variable, else 200 (`default_counterexamples`).
        params: Values for the `ibis.param`s of an Ibis transform, as Ibis's
            `execute(params=...)` takes them. The report is about the
            transform with these values (`bind_params`); an unbound parameter
            is refused.
        semantics: What the SQL `verify` lifts means, the transformation
            if it is a SQL string and every SQL condition: `"reference"`
            (the default), sverify's reference semantics, where an
            operation that would create a NaN raises; or `"duckdb"`, what
            DuckDB computes, NaN and ±inf included. An `sv.sql` expression
            inside an Ibis transformation keeps its own `semantics`. Unstated
            (None), it is `"duckdb"` for a transformation whose SQL is all
            `sv.sql(..., semantics="duckdb")`, else `"reference"`.
            `"polars"` checks an Ibis transformation under Polars's
            profile (#444), `"spark"` under Spark's (#739): its plan runs
            natively on that engine (`sverify.routes`, the route
            `"native"`).
            `"substrait"` checks an Ibis transformation under Substrait's
            own semantics (`Profile.substrait`, #444): the proof under the
            reference holds there where Substrait allows nothing more at
            the options the plan meets, and `Report.transfer` names the
            options where it allows more.
        on_inferred: What a precondition sverify infers does. sverify
            infers the bounds on input columns that rule out integer
            overflow (`infer_bounds`: `amount * 2` on BIGINT needs
            `_.amount < 2**62`) and the `IS NOT NULL`s a postcondition
            needs (`Report.inferred`). `"error"` (the default): the plan is
            not proved without it, and the report says where it came from
            and how to state it (`Report.needed`). `"warn"`: it is assumed,
            checked on the data before each run, and a warning names it
            (`sverify.errors.InferredWarning`). `"ignore"`: it is assumed and
            checked without a warning. `"off"`: nothing is inferred or
            assumed, so an integer `SUM` that may leave 64 bits, or a double
            operation that may overflow to ±inf, is an error too, which the
            other values check on the data while the job runs
            (`Report.assumed`); each `Issue.hint` suggests a bound.
            `"silent"` is a deprecated spelling of `"ignore"`.

    Returns:
        A `Report` with the status of each postcondition, the possible
        runtime errors, and what is known about each output column.

    Raises:
        ValueError: `requires` names an unknown table, `unique` or
            `references` names an unknown column or table, or the checker
            fails on the request (for example on a plan outside the Lean
            model).

    Examples:
        A SQL query (DuckDB's SQL), with its input schema:

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
    transform = query
    on_inferred = _checked_on_inferred(on_inferred)
    bound: list[str] = []
    if params:
        if isinstance(transform, str):
            raise TypeError("params bind the ibis.param values of an Ibis expression, not SQL")
        transform = bind_params(transform, params)
        bound = [
            f"param{k} ({p.type()}) = {v!r}" for k, (p, v) in enumerate(params.items(), start=1)
        ]
    inputs = list(tables or {})
    if not isinstance(transform, str):
        inputs += [t for t in leaf_tables(transform) if t not in inputs]
    if semantics is None:
        semantics = _expr_semantics(transform)
    return infer_bounds(
        transform,
        requires=requires_by_input(requires, inputs),
        ensures=expand_keys(ensures),
        tables=tables,
        counterexamples=default_counterexamples() if counterexamples is None else counterexamples,
        params=bound,
        infer=on_inferred != "off",
        semantics=_checked_semantics(semantics),
        on_inferred=on_inferred,
    )


def input_schema(s: Any) -> ibis.Schema:
    """An input of `verify(tables=...)` as an Ibis schema: an Ibis table or
    schema, or a mapping of column names to types, each an Ibis type or
    type name (`"int64"`, `"!string"`) or DuckDB's (`"BIGINT"`, `"HUGEINT"`,
    `"VARCHAR NOT NULL"`), as `CREATE TABLE` and `DESCRIBE` write them."""
    if isinstance(s, ir.Table):
        return s.schema()
    if isinstance(s, ibis.Schema) or not isinstance(s, Mapping):
        return ibis.schema(s)
    return ibis.schema({c: _column_type(c, t) for c, t in s.items()})


def _column_type(col: str, t: Any) -> Any:
    """`t` as an Ibis type: Ibis's own names first, then DuckDB's."""
    if not isinstance(t, str):
        return t
    try:
        return ibis.dtype(t)
    except Exception:  # noqa: BLE001 - Ibis raises several kinds
        pass
    from ibis.backends.sql.datatypes import DuckDBType

    text = t.strip()
    m = re.fullmatch(r"(.*?)\s+NOT\s+NULL", text, re.IGNORECASE)
    unknown = ValueError(
        f"tables: column {col!r} has type {t!r}, which is neither an Ibis type nor one of DuckDB's"
    )
    try:
        dtype = DuckDBType.from_string(m[1] if m else text)
    except Exception as e:  # noqa: BLE001
        raise unknown from e
    if dtype.is_unknown():
        raise unknown
    return dtype.copy(nullable=not m)


def infer_bounds(
    transform: Transform,
    *,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    counterexamples: int,
    params: list[str],
    infer: bool = True,
    inputs: Collection[str] | None = None,
    semantics: Semantics = "reference",
    on_inferred: OnInferred = "ignore",
) -> Report:
    """`verify`, with the bounds that rule out overflow inferred (#244).

    Lean's `SubstraitLean/Infer.lean` runs the range analysis backwards: for
    each overflow it may not rule out, the range of each input column that
    does (`amount * 2` on BIGINT fits when `amount < 2**62`). Those bounds
    are candidates only. The ones on the tables in `assume` (all tables if
    None) are added to `requires`, rounded inward to round numbers, and the
    contract is proved again, as if the user had written them: a wrong bound
    makes that proof fail, never pass wrongly. For the rest, and for
    overflows without a unique bound (the product of two columns), the
    report's `Issue.hint` suggests one.

    `inputs` are the tables whose preconditions the caller states (None:
    all): their bounds are assumed with `infer`, and suggested for
    `requires`; bounds on other tables (results of other contracted
    transformations) are suggested for those tables' `ensures`.

    An observation in `ensures` (`sv.equivalent`) is no condition to prove:
    it goes to `Report.observation`, and each other postcondition that
    depends on what it ignores says so (`CheckedCondition.ignores`)."""
    observed, ensures = _observation.split(ensures)
    report = _infer_bounds(
        transform,
        requires,
        ensures,
        tables,
        counterexamples,
        params,
        infer,
        inputs,
        semantics,
        observed or _observation.PLAN_BOUND,
    )
    conditions = {t: list(cs) for t, cs in requires.items()}
    _merge(conditions, report._inferred)
    report._conditions = conditions
    opened = {} if report._windows_total or isinstance(transform, str) else _open_columns(transform)
    out = _observed(report, observed or _observation.PLAN_BOUND, ensures, opened)
    out._stated = observed is not None
    from sverify import routes as _routes

    if out.observation.floats == "plan":
        out.observation = replace(out.observation, bound=_routes.plan_bound(out._epsilon))
    else:
        out._floats_on = _routes.floats_on(out)
    out._on_inferred = _checked_on_inferred(on_inferred)
    if on_inferred == "off" and out._margin_checks:
        # Nothing is checked on the data: a threshold filter on a double sum
        # may keep other groups than the reference's (#568).
        out._margin_checks = []
        out._rows_exact = dict.fromkeys(out._rows_exact or {}, False)
    if not out.deterministic and not isinstance(transform, str):
        out.ties = _confirmed_ties(transform, requires, out, tables, params, inputs, semantics)
    if on_inferred == "warn" and out._inferred:
        warnings.warn(
            InferredWarning(
                "assumed inferred precondition(s): "
                + "; ".join(
                    n.split(": declare")[0]
                    for n in out._needs_lines(
                        {t: [label(c) for c in cs] for t, cs in out._inferred.items()}
                    )
                ),
                out,
            ),
            stacklevel=3,
        )
    return out


OnUnproved = Literal["error", "check", "warn"]


class InferredWarning(SverifyWarning):
    """A precondition sverify inferred is assumed (`on_inferred="warn"`).

    Attributes:
        report: The `Report` whose `inferred` preconditions are assumed.
    """

    def __init__(self, message: str, report: Report | None = None):
        super().__init__(message)
        self.report = report


class UnprovedWarning(SverifyWarning):
    """A transform with `on_unproved="warn"` is built although its contract
    is not proved; its refreshes run unverified (`UnverifiedRunWarning`).

    Attributes:
        report: The `Report` that is not proved.
    """

    def __init__(self, message: str, report: Report | None = None):
        super().__init__(message)
        self.report = report


def __getattr__(name: str) -> Any:
    if name == "InferredPreconditionWarning":
        warnings.warn(
            "InferredPreconditionWarning is deprecated; catch sverify.errors.InferredWarning",
            DeprecationWarning,
            stacklevel=2,
        )
        return InferredWarning
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def _checked_on_inferred(v: str) -> OnInferred:
    if v == "silent":
        warnings.warn(
            'on_inferred="silent" is deprecated; write on_inferred="ignore"',
            DeprecationWarning,
            stacklevel=4,
        )
        return "ignore"
    if v not in ("error", "warn", "ignore", "off"):
        raise ValueError(f"on_inferred must be 'error', 'warn', 'ignore' or 'off', not {v!r}")
    return v  # type: ignore[return-value]


def _checked_on_unproved(v: str) -> OnUnproved:
    """`on_unproved`, with the deprecated `"runtime"` read as `"check"`."""
    if v == "runtime":
        warnings.warn(
            'on_unproved="runtime" is deprecated; write on_unproved="check"',
            DeprecationWarning,
            stacklevel=3,
        )
        return "check"
    if v not in ("error", "check", "warn"):
        raise ValueError(f"on_unproved must be 'error', 'check' or 'warn', not {v!r}")
    return v  # type: ignore[return-value]


def _observed(
    report: Report,
    observed: Observation,
    ensures: Sequence[Condition],
    opened: Mapping[str, str],
) -> Report:
    """`report` with the observation, and each postcondition marked with the
    components it depends on that the observation ignores, or that the plan
    leaves open (D1, D12): the checker's (`ContractCheck`'s `Report.ignores`,
    #1071) for every postcondition it reports them for. A table condition
    (`unique`, `references`, `max_rows`, `rows_per`), which the checker does
    not evaluate as an expression, depends on the values of the columns it
    reads (`observation.dependencies`), and on the open choices of the plan
    (`opened`) where it is unproved: a proved condition holds for every
    choice the plan leaves open."""
    checked = [
        replace(
            c,
            reads=None if (r := _reads(cond, report.output)) is None else tuple(r),
            approx=isinstance(cond, Approx),
            nullable=None
            if r is None or any(c not in report.facts for c in r)
            else tuple(c for c in r if "NULL" in report.facts[c]),
            ignores=c.checker_ignores
            if c.checker_ignores is not None
            else tuple(
                _observation.dependencies(
                    observed, cond, report.output, r, {} if c.proved else opened
                )
            ),
        )
        for cond, c in zip(ensures, report.ensures, strict=True)
    ]
    return replace(report, ensures=checked, observation=observed)


def _open_columns(expr: ir.Table) -> dict[str, str]:
    """The output columns of aggregates whose value the reference leaves
    open: `"picks"` for `first`, `last` or `arbitrary` without an order,
    `"elements"` for `collect` or `group_concat` without one."""
    out: dict[str, str] = {}
    for agg in expr.op().find(ops.Aggregate):
        if not isinstance(agg, ops.Aggregate):
            continue
        for name, metric in agg.metrics.items():
            if (
                isinstance(metric, ops.First | ops.Last)
                and not metric.order_by
                or isinstance(metric, ops.Arbitrary)
            ):
                out[name] = "picks"
            elif isinstance(metric, ops.ArrayCollect | ops.GroupConcat) and not metric.order_by:
                out[name] = "elements"
    names = set(expr.columns)
    return {n: why for n, why in out.items() if n in names}


def _reads(cond: Condition, columns: Mapping[str, Any]) -> list[str] | None:
    """The output columns `cond` reads; None where that is not known."""
    if isinstance(cond, Unique | RowsPer):
        return list(cond.cols)
    if isinstance(cond, References | ArrivesWithin):
        return [cond.col]
    if isinstance(cond, MaxRows):
        return []
    if isinstance(cond, Approx):
        return _reads(cond.cond, columns)
    if isinstance(cond, str):
        import sqlglot
        from sqlglot import exp

        try:
            parsed = sqlglot.parse_one(cond, read="duckdb")
        except sqlglot.errors.ParseError:
            return None
        return [c.name for c in parsed.find_all(exp.Column)]
    if not columns:
        return None
    try:
        expr = resolve(cond, ibis.table(ibis.schema(dict(columns)), name="t"))
        return [f.name for f in expr.op().find(ops.Field) if isinstance(f, ops.Field)]
    except Exception:  # noqa: BLE001 - an unreadable condition reads every column
        return None


def _infer_bounds(
    transform: Transform,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    counterexamples: int,
    params: list[str],
    infer: bool,
    inputs: Collection[str] | None,
    semantics: Semantics,
    observed: _observation.Observation | None = None,
) -> Report:
    def once(reqs: Mapping[str, Sequence[Condition]], n: int):
        return _verify_once(
            transform, reqs, ensures, tables, n, params, inputs, semantics, observed
        )

    def finish(report: Report, schemas: Mapping[str, Any], widened) -> Report:
        """The reasons and hints each confirmed by a proof (#688)."""

        def proves(cond: Condition) -> bool:
            again = _verify_once(transform, widened, [cond], tables, 0, params, inputs, semantics)
            return all(e.proved for e in again[0].ensures)

        report = _confirm_suggestions(report, requires, once)
        report = _key_reasons(transform, report, requires, ensures, schemas, inputs, once)
        report = _null_reasons(transform, report, ensures, proves)
        return _confirm_hints(report, requires, once)

    if not infer:
        report, _raw, schemas = once(requires, counterexamples)
        return finish(report, schemas, requires)
    # Counterexamples only for the final proof.
    report, raw, schemas = once(requires, 0)
    extra = {
        t: cs for t, cs in _render_needs(raw, schemas).items() if inputs is None or t in inputs
    }
    if extra:
        guarded = and_or_hints(report.issues, transform)
        widened = {t: list(cs) for t, cs in requires.items()}
        _merge(widened, extra)
        first = report.issues
        report = once(widened, counterexamples)[0]
        report._inferred = {t: list[Condition](cs) for t, cs in extra.items()}
        report._inferred_from = {
            label(c): i
            for cs in extra.values()
            for c in cs
            for i in reversed(first)
            if label(c) in i._labels
        }
        # An inferred precondition that a guard under AND/OR would have made
        # unnecessary with a CASE (#604): say so.
        report._hints += [h for h in guarded if h not in report._hints]
    elif counterexamples and report.unproved:
        report = once(requires, counterexamples)[0]
    report = _null_preconditions(transform, report, requires, ensures, inputs, once)
    widened = {t: list(cs) for t, cs in requires.items()}
    _merge(widened, report._inferred)
    report = finish(report, schemas, widened)
    # A SUM that may overflow is assumed to fit, and an operation on finite
    # doubles to stay finite (#575), both checked on the data while the job
    # runs: the row caps (#219) and the bounds do not rule them out.
    report.assumed = [i for i in report.issues if _assumable(i)]
    report.issues = [i for i in report.issues if not _assumable(i)]
    return report


#: The kind an inferred `IS NOT NULL` names as its source (#655).
NULL_KIND = "a NULL result"


def _null_preconditions(
    transform: Transform,
    report: Report,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    inputs: Collection[str] | None,
    once: Callable[..., Any],
) -> Report:
    """`report` with the `IS NOT NULL` preconditions that prove a
    postcondition failing only on NULL (`TRUE or NULL`), inferred like the
    bounds (#655): for each column it reads that passes on an input
    column, `_.<column>.notnull()` on that input, kept if the postcondition
    is then proved. A postcondition that may also be FALSE gets none."""
    if isinstance(transform, str):
        return report
    found: dict[str, list[Condition]] = {}
    source: dict[str, Issue] = {}
    by_label = {label(c): c for c in ensures if not isinstance(c, TableCondition)}
    root = transform.op()
    for c in report.ensures:
        cond = by_label.get(c.label)
        if c.proved or cond is None:
            continue
        if set(c.value.replace(" or ", ", ").split(", ")) != {"TRUE", "NULL"}:
            continue
        for t, base in _input_columns(root, _reads(cond, report.output) or []):
            if inputs is not None and t not in inputs:
                continue
            new = getattr(ibis._, base).notnull()
            if label(new) in {label(x) for x in [*requires.get(t, []), *found.get(t, [])]}:
                continue
            found.setdefault(t, []).append(new)
            source[label(new)] = Issue(NULL_KIND, c.label, False, shown=c.label)
    if not found:
        return report
    widened = {t: list(cs) for t, cs in requires.items()}
    _merge(widened, report._inferred)
    _merge(widened, found)
    again = once(widened, 0)[0]
    proved = {e.label for e in again.ensures if e.proved}
    if not all(c.proved or c.label in proved for c in report.ensures if c.label in by_label):
        # Only where it proves every postcondition that failed on NULL alone.
        kept_for = {iss.expr for iss in source.values() if iss.expr in proved}
        found = {t: [x for x in cs if source[label(x)].expr in kept_for] for t, cs in found.items()}
        found = {t: cs for t, cs in found.items() if cs}
        if not found:
            return report
        widened = {t: list(cs) for t, cs in requires.items()}
        _merge(widened, report._inferred)
        _merge(widened, found)
        again = once(widened, 0)[0]
    inferred = {t: list(cs) for t, cs in report._inferred.items()}
    _merge(inferred, found)
    again._inferred = inferred
    again._inferred_from = {**report._inferred_from, **source}
    again._hints = report._hints
    return again


def _confirm_hints(report: Report, requires, once) -> Report:
    """`report` with only the hints a proof confirms (#688): each possible
    runtime error whose hint proposes preconditions is verified again with
    them added to `requires` (and to what was inferred), and its hint is
    dropped if the error remains."""
    tried: dict[str, set[tuple[str, str]]] = {}
    issues = []
    for i in report.issues:
        if i.hint_needs:
            key = repr(sorted((t, sorted(label(c) for c in cs)) for t, cs in i.hint_needs.items()))
            if key not in tried:
                widened = {t: list(cs) for t, cs in requires.items()}
                _merge(widened, report._inferred)
                _merge(widened, i.hint_needs)
                again = once(widened, 0)[0]
                tried[key] = {(j.kind, j.expr) for j in again.issues if j.error}
            if (i.kind, i.expr) in tried[key]:
                i = replace(i, hint=i.unconfirmed, hint_needs={}, unconfirmed=None, needs=[])
        issues.append(i)
    return replace(report, issues=issues)


def _key_sources(
    transform: Transform, cols: Sequence[str], schemas: Mapping[str, Any]
) -> tuple[str, list[str]] | None:
    """The input table and its columns an output key comes from: traced
    through an Ibis expression, or for SQL, the one input with every column
    of the same name."""
    if isinstance(transform, str):
        origins = [_sql_origin(transform, c, schemas) for c in cols]
    else:
        origins = [_origin(transform.op(), c) for c in cols]
    if any(o is None for o in origins) or len({o[0] for o in origins if o}) != 1:
        return None
    return origins[0][0], [o[1] for o in origins if o]  # type: ignore[index]


def _sql_origin(sql: str, col: str, schemas: Mapping[str, Any]) -> tuple[str, str] | None:
    """The input table and column a SQL query's output column passes on
    unchanged (SQLGlot's lineage), if there is one."""
    import sqlglot.expressions as exp
    from sqlglot.lineage import lineage

    try:
        schema = {t: {c: str(d) for c, d in sch.items()} for t, sch in schemas.items()}
        root = lineage(col, sql, schema=schema, dialect="duckdb")
        nodes = list(root.walk())
    except Exception:  # noqa: BLE001 - no lineage, no origin
        return None
    leaves = [n for n in nodes if not n.downstream]
    for n in nodes:
        e = n.expression.this if isinstance(n.expression, exp.Alias) else n.expression
        if not isinstance(e, exp.Column | exp.Table):
            return None
    if len(leaves) != 1 or not isinstance(leaves[0].source, exp.Table):
        return None
    table = leaves[0].source.name
    return (table, leaves[0].name.split(".")[-1]) if table in schemas else None


def _key_reasons(
    transform: Transform,
    report: Report,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    schemas: Mapping[str, Any],
    inputs: Collection[str] | None,
    once: Callable[..., Any],
) -> Report:
    """`report` with the reason each unproved `unique(...)` is not a key, in
    terms of the input it comes from (#688): declare the input's key where
    that proves it (checked), say the key is lost on the way where it is
    already declared, or that no key on an input reaches the column."""
    keys = {label(c): c for c in ensures if isinstance(c, Unique)}
    ensured = []
    for c in report.ensures:
        key = keys.get(c.label)
        if c.proved or key is None:
            ensured.append(c)
            continue
        src = _key_sources(transform, key.cols, schemas)
        out = ", ".join(f"`{x}`" for x in key.cols)
        if src is None:
            reason = (
                f"{out} {'is' if len(key.cols) == 1 else 'are'} computed, or "
                f"{'comes' if len(key.cols) == 1 else 'come'} from several inputs, "
                "and no key on an input makes it a key here"
            )
        else:
            t, base = src
            want = unique(*base)
            where = ", ".join(f"{t}.{b}" for b in base)
            stated = {label(x) for x in requires.get(t, [])}
            came = f"{out} {'comes' if len(key.cols) == 1 else 'come'} from {where}"
            if want.label in stated:
                reason = (
                    f"{came}, whose key {want.label} is lost on the way: a join, a union "
                    "or an UNNEST can repeat a value"
                )
            elif inputs is not None and t not in inputs:
                reason = f"{came}, which has no key on it"
            else:
                widened = {k: list(v) for k, v in requires.items()}
                _merge(widened, report._inferred)
                widened.setdefault(t, []).append(want)
                again = once(widened, 0)[0]
                if any(e.label == c.label and e.proved for e in again.ensures):
                    code = "sv.unique(" + ", ".join(repr(b) for b in base) + ")"
                    reason = f"{came}: declare `{code}` in the requires of {t!r}"
                else:
                    reason = (
                        f"{came}, and a key there does not make it one here: a join or a "
                        "union can repeat a value"
                    )
        ensured.append(replace(c, detail=f"the preconditions do not make it a key: {reason}"))
    return replace(report, ensures=ensured)


def _null_reasons(
    transform: Transform,
    report: Report,
    ensures: Sequence[Condition],
    proves: Callable[[Condition], bool],
) -> Report:
    """`report` with a way out for each postcondition that fails only on
    NULL (#688): allowing NULL in the column that is NULL, as code in the
    transformation's language, where the checker proves the condition so
    relaxed."""
    conds = {label(c): c for c in ensures if not isinstance(c, TableCondition)}
    ensured = []
    for c in report.ensures:
        cond = conds.get(c.label)
        parts = set(c.value.replace(" or ", ", ").split(", "))
        if c.proved or cond is None or c.detail or "FALSE" in parts or "NULL" not in parts:
            ensured.append(c)
            continue
        cols = c.nullable if c.nullable is not None else _reads(cond, report.output) or ()
        for col in [x for x in cols if "NULL" in report.facts.get(x, "NULL")]:
            if isinstance(cond, str) and isinstance(transform, str):
                relaxed: Condition = f"({cond}) OR {col} IS NULL"
                code = relaxed
            elif isinstance(cond, Deferred):
                relaxed = cond | getattr(ibis._, col).isnull()
                code = label(relaxed)
            else:
                continue
            if proves(relaxed):
                c = replace(
                    c,
                    detail=(
                        f"it may be NULL on some rows, where {col} is NULL: to allow that, "
                        f"state `{code}`"
                    ),
                )
                break
        ensured.append(c)
    return replace(report, ensures=ensured)


def _confirm_suggestions(report: Report, requires, once) -> Report:
    """`report` with only the suggestions a proof confirms: each unproved
    postcondition's suggested preconditions are added to `requires` (and to
    what was inferred), and kept if the postcondition is then proved."""
    ensures = []
    for c in report.ensures:
        if c.suggested:
            widened = {t: list(cs) for t, cs in requires.items()}
            _merge(widened, report._inferred)
            _merge(widened, c.suggested)
            again = once(widened, 0)[0]
            if not any(e.label == c.label and e.proved for e in again.ensures):
                c = replace(c, suggested={})
        ensures.append(c)
    return replace(report, ensures=ensures)


def _verify_once(
    transform: Transform,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    counterexamples: int,
    bound: list[str],
    inputs: Collection[str] | None,
    semantics: Semantics = "reference",
    observed: _observation.Observation | None = None,
) -> tuple[Report, list[dict], dict[str, ibis.Schema]]:
    """One proof (see `verify`), with the bounds Lean inferred and the input
    schemas."""
    if semantics in _profile_requests() and isinstance(transform, str):
        raise ValueError(
            f"semantics={semantics!r} checks Ibis transformations; "
            "SQL is DuckDB's, so its semantics is 'duckdb' or 'reference'"
        )
    schemas = {name: input_schema(s) for name, s in (tables or {}).items()}
    if not isinstance(transform, str):
        schemas = {**leaf_tables(transform), **schemas}
    con = connect()
    for name, schema in schemas.items():
        con.create(name, schema)

    def lift(query: Any) -> Semantics:
        # A SQL condition (an inferred bound, say) is DuckDB's SQL, lifted
        # under the reference where the profile has no lift of its own.
        own = not (isinstance(query, str) and semantics in _profile_requests())
        return semantics if own else "reference"

    def plan(query: Transform) -> Any:
        return json.loads(plan_json(con, query, lift(query)))

    def table_ref(name: str, cond: Condition) -> Transform:
        if isinstance(transform, str) and isinstance(cond, str):
            return f"SELECT * FROM {q(name)}"
        return con.table(name)

    def output(cond: Condition) -> Transform:
        """The transformation as `cond` reads it: an Ibis condition on a SQL
        transformation reads the lifted query as an Ibis relation over the
        input tables, as in an `sv.sql` body (#438)."""
        if not isinstance(transform, str) or isinstance(cond, str):
            return transform
        from sverify.ibis_substrait import SQLModel, sql_model_schema

        names = tuple(schemas)
        inputs: Any = tuple(con.table(n).op() for n in names)
        return SQLModel(
            transform,
            inputs,
            names,
            sql_model_schema(transform, schemas, semantics),
            "duckdb",
            semantics,
        ).to_expr()

    req_conds = [
        (t, c) for t, cs in requires.items() for c in cs if not isinstance(c, TableCondition)
    ]

    def query(where: str, n: int, table: Transform, c: Condition) -> Transform:
        """`condition_query`, with an Ibis error named by the condition it
        is in (#687)."""
        from ibis.common.exceptions import IbisError

        try:
            return condition_query(table, c, lift(c))
        except IbisError as e:
            msg = f"{where} condition {n}, {label(c)}, does not type-check: {e}"
            try:
                err = type(e)(msg)
            except Exception:  # noqa: BLE001 - an error class with another signature
                err = TypeError(msg)
            raise err from e

    req_plans = []
    for t, cs in requires.items():
        for n, c in enumerate(cs, start=1):
            if not isinstance(c, TableCondition):
                req_plans.append(plan(query(f"requires {t}", n, table_ref(t, c), c)))
    ens_plans = []
    for n, c in enumerate(ensures, start=1):
        if isinstance(c, TableCondition):
            continue
        p = plan(query("ensures", n, output(c), c))
        p["relations"][0]["root"]["names"] = [label(c)]
        ens_plans.append(p)
    transform_plan = plan(transform)
    out_cols: list[str] = transform_plan["relations"][0]["root"]["names"]

    def names(t: str) -> Sequence[str]:
        return column_names(schemas[t])

    def entries(kind: str) -> dict[str, list]:
        return {
            t: [
                c.plan_entry(t, names)
                for c in cs
                if isinstance(c, TableCondition) and c.entry == kind
            ]
            for t, cs in requires.items()
        }

    keys = entries("keys")
    ensures_keys = [_positions(c.cols, out_cols) for c in ensures if isinstance(c, Unique)]
    foreign_keys = entries("references")
    caps = {t: min(ns) for t, ns in entries("max_rows").items() if ns}
    per_key = {t: ps for t, ps in entries("rows_per").items() if ps}
    contract = {
        "requires": req_plans,
        "ensures": ens_plans,
        "transform": transform_plan,
        "keys": keys,
        "ensures_keys": ensures_keys,
        "references": foreign_keys,
        "max_rows": caps,
        "rows_per": per_key,
    }

    if observed is not None:
        # What the checker needs to report each postcondition's ignored
        # components itself (#1071, `Report.ignores` in ContractCheck.lean).
        contract["observation"] = {
            "coarsens": [c for c in observed.ignored()],
            "floats_plan": observed.floats == "plan",
            "approx": [isinstance(c, Approx) for c in ensures if not isinstance(c, TableCondition)],
            "sql": isinstance(transform, str),
        }
    if semantics in _profile_requests():
        contract["profile"] = semantics
    code, stdout, stderr = run_checker(("--contract",), json.dumps(contract))
    if code not in (0, 4):
        raise checker_failed("--contract", stderr)
    out = json.loads(stdout)
    if semantics in _profile_requests() and out.get("profile") != semantics:
        raise ValueError(
            f'the checker in use has no profile "{semantics}": install the package that '
            "registers it (sverify.profiles), or set SVERIFY_CHECKER to a checker built with it"
        )
    # SQL's types come from the lift, so a timestamp is described as one (#452).
    from sverify.ibis_substrait import sql_model_schema

    result = (
        sql_model_schema(transform, schemas, semantics)
        if isinstance(transform, str)
        else transform.schema()
    )
    dtypes = dict(result.items())

    def describe(f: dict) -> str:
        dtype = dtypes.get(f["name"])
        return (render_fact(f["abstract"], dtype) if dtype is not None else None) or f["value"]

    assumable: Container[str] = schemas if inputs is None else inputs
    rows = iter(out["ensures"])
    # Per postcondition, whether it holds on every engine's doubles (#1045).
    robust = iter(out.get("robust") or [])
    key_results = iter(out["keys"])
    req_named = [(t, p) for (t, _), p in zip(req_conds, req_plans, strict=True)]
    ens_iter = iter(ens_plans)
    key_iter = iter(ensures_keys)

    def find(target: dict | Sequence[int]) -> Counterexample | None:
        if not counterexamples:
            return None
        with _stages.stage("counterexamples"):
            return search_counterexample(
                schemas,
                req_named,
                keys,
                transform_plan,
                target,
                budget=counterexamples,
                references=foreign_keys,
            )

    def next_key() -> tuple[bool, Counterexample | None]:
        ok = next(key_results)["proved"]
        cols = next(key_iter)
        return ok, None if ok else find(cols)

    checked = []
    for c in ensures:
        if isinstance(c, TableCondition):
            checked.append(c.ensured(out, next_key))
        else:
            e = next(rows)
            p = next(ens_iter)
            rb = next(robust, None) or {}
            holds_on_engines = bool(rb.get("robust")) if isinstance(rb, dict) else bool(rb)
            proved_on = tuple(rb.get("proved_on") or ()) if isinstance(rb, dict) else ()
            ties = bool(e.get("ties"))
            # It depends on how ties are ordered, which the search, on
            # `Rel.eval`'s one order, rarely shows; breaking the ties with
            # a key proves it (#691).
            cex = None if e["proved"] or ties else find(p)
            suggested = _suggested(e.get("suggest"), schemas, assumable)
            depends = e.get("depends")
            checked.append(
                CheckedCondition(
                    e["name"],
                    e["proved"],
                    e["value"],
                    cex,
                    suggested=suggested,
                    ties=ties,
                    depends=None if depends is None else tuple(depends),
                    allowed=bool(e.get("allowed")),
                    robust=holds_on_engines,
                    robust_on=proved_on,
                    checker_ignores=None if (ig := e.get("ignores")) is None else tuple(ig),
                )
            )
        checked[-1].condition = c
    from sverify import _user_text

    dialect: _user_text.Dialect = "sql" if isinstance(transform, str) else "ibis"
    seen = _user_text.columns(transform_plan)
    temporal = {
        c for sch in [*schemas.values(), result] for c, t in sch.items() if t.is_timestamp()
    }

    def shown(e: str, measure: bool = False) -> str | None:
        n = _user_text.named(e, transform_plan, measure, seen)
        return None if n is None else _user_text.pretty(n, dialect, temporal)

    def show(e: str) -> str:
        return shown(e) or e

    raw_issues = [
        i
        for i in out["issues"]
        # An overflow to ±∞ is the reference's precondition (#575): DuckDB's
        # semantics allows it, as DuckDB gives ±∞.
        if semantics == "reference" or i["kind"] != INFINITE
    ]
    report = Report(
        semantics=semantics,
        _dialect=dialect,
        requires={t: [label(c) for c in cs] for t, cs in requires.items()},
        ensures=checked,
        facts={f["name"]: describe(f) for f in out["facts"]},
        not_null=[
            f["name"]
            for f in out["facts"]
            if f["name"] in dtypes and f.get("abstract", {}).get("null") is False
        ],
        deterministic=out["deterministic"],
        _windows_total=out.get("windows_total", out["deterministic"]),
        _tie_places=tie_places(out),
        issues=_issues(
            raw_issues,
            # Ibis's `//` and `%` floor, and the producer writes them in the
            # reference's form (`floorDivOf`), as does a FLOOR option.
            floor=dialect == "ibis" or '"FLOOR"' in json.dumps(transform_plan),
            hint=lambda b: _hint(b, schemas, assumable, show),
            needs=lambda b: _render_needs(b["needs"], schemas),
            column=lambda e: _sum_column(transform, e),
            shown=shown,
            guess=lambda e: _guess_bounds(e, schemas, assumable, dialect),
            dialect=dialect,
        ),
        _guard_free=out["guard_free"],
        _unchecked=out.get("unchecked"),
        _optimized=out["optimized"],
        _rewrites=out["rewrites"],
        _params=bound,
        _bounds=_int_bounds(out["facts"], dtypes),
        rows=out.get("rows"),
        _relations=[
            RelationRows(r["op"], r["depth"], r["rows"], r["group_rows"])
            for r in out.get("relations", [])
        ],
        _implied=_implied_sql(out.get("implied", []), schemas),
        internal_plan=json.dumps(transform_plan),
        _depends=out.get("depends"),
        _epsilon=out.get("epsilon"),
        _rows_exact=out.get("rows_exact"),
        _margin_checks=list(out.get("margin_checks") or []),
        _contract=contract,
        _transfer=(out.get("transfer") or {}).get("failures") if semantics == "substrait" else None,
        output=dtypes,
        _postconditions=list(ensures),
        inputs=dict(schemas),
    )
    if not isinstance(transform, str) and report.issues:
        report._hints = overflow_hints(transform, requires, report)
    report._hints += and_or_hints(report.issues, transform)
    if not isinstance(transform, str):
        report._hints += rounding_hints(transform, ensures, checked, out["facts"], dtypes)
        if semantics != "polars":
            report._hints += division_hints(transform)
    return report, out["inferred"], schemas


def _guess_bounds(
    shown: str, schemas: Mapping[str, ibis.Schema], assumable: Container[str], dialect: str
) -> dict[str, list[Condition]]:
    """Bounds on the input columns an expression names, wide enough for
    most data: timestamps and dates in [1900, 2200), integers within ±10⁹,
    doubles and decimals within ±10⁶.
    A hint proposes them only where a proof confirms they rule its issue
    out (`_confirm_hints`, #688)."""
    names = set(re.findall(r"(?<![\w.'\"])([A-Za-z_]\w*)\b(?!\s*\()", shown))
    names |= set(re.findall(r"\w+\(([A-Za-z_]\w*)\)", shown))
    out: dict[str, list[Condition]] = {}
    for t, schema in schemas.items():
        if t not in assumable:
            continue
        for col, dtype in schema.items():
            if col not in names:
                continue
            q = f'"{col}"' if not col.isidentifier() else col
            if dtype.is_timestamp() or dtype.is_date():
                ctor, sql = ("datetime", "TIMESTAMP") if dtype.is_timestamp() else ("date", "DATE")
                lo, hi = (datetime, datetime) if ctor == "datetime" else (date, date)
                conds: list[Condition] = (
                    [getattr(ibis._, col) >= lo(1900, 1, 1), getattr(ibis._, col) < hi(2200, 1, 1)]
                    if dialect == "ibis"
                    else [f"{q} >= {sql} '1900-01-01'", f"{q} < {sql} '2200-01-01'"]
                )
            elif dtype.is_integer():
                conds = (
                    [getattr(ibis._, col) >= -1_000_000_000, getattr(ibis._, col) <= 1_000_000_000]
                    if dialect == "ibis"
                    else [f"{q} >= -1000000000", f"{q} <= 1000000000"]
                )
            elif dtype.is_floating() or dtype.is_decimal():
                conds = (
                    [getattr(ibis._, col) >= -1_000_000, getattr(ibis._, col) <= 1_000_000]
                    if dialect == "ibis"
                    else [f"{q} >= -1000000", f"{q} <= 1000000"]
                )
            else:
                continue
            out.setdefault(t, []).extend(conds)
    return out


def _merged_bound(bounds: Sequence[dict | None]) -> dict | None:
    """One inference result for the issues reported as one (`_issues`): the
    bounds each needs, the tightest per column, where every one has bounds;
    else the first reason none does."""
    if len(bounds) == 1:
        return bounds[0]
    found = [b for b in bounds if b is not None]
    if len(found) < len(bounds):
        return next((b for b in found if b["why"] is not None), None)
    if why := next((b for b in found if b["why"] is not None), None):
        return why
    ranges: dict[tuple[str, int], dict] = {}
    other: list[dict] = []
    for b in found:
        for n in b["needs"]:
            if "lo" not in n and "hi" not in n:
                if n not in other:
                    other.append(n)
                continue
            have = ranges.setdefault((n["table"], n["col"]), {**n})
            for k, pick in (("lo", max), ("hi", min)):
                vals = [int(v) for v in (have.get(k), n.get(k)) if v is not None]
                have[k] = str(pick(vals)) if vals else None
    return {
        "why": None,
        "split": any(b["split"] for b in found),
        "needs": [*ranges.values(), *other],
    }


def _issues(
    raw: Sequence[dict],
    floor: bool,
    hint: Callable[[dict | None], str | None],
    needs: Callable[[dict], Mapping[str, Sequence[Inferred]]],
    column: Callable[[str], str | None],
    shown: Callable[..., str | None],
    guess: Callable[[str], dict[str, list[Condition]]] = lambda e: {},
    dialect: str = "ibis",
) -> list[Issue]:
    """The checker's issues, one per expression the user wrote and kind
    (#687): the sub-expressions of an expression that may overflow, and the
    branches of the reference's form of a floor division (`_user_text.fold`),
    are reported as the expression, with the bounds that rule out all of
    them."""
    from sverify._user_text import fold

    groups: dict[tuple[str, str], list[dict]] = {}
    for kind in dict.fromkeys(i["kind"] for i in raw):
        members = [i for i in raw if i["kind"] == kind]
        for i, key in zip(members, fold([i["expr"] for i in members], floor), strict=True):
            groups.setdefault((kind, key), []).append(i)
    out = []
    for (kind, expr), members in groups.items():
        error = any(i["error"] for i in members) or kind == INFINITE
        constant = any(i.get("constant", False) for i in members)
        bound = _merged_bound([i["bound"] for i in members])
        if constant:
            text = CONSTANT_HINT
        elif any(i["error"] for i in members):
            text = hint(bound)
        else:
            text = INFINITE_HINT if kind == INFINITE else None
        code: Mapping[str, Sequence[Condition]] = (
            needs(bound) if bound and bound.get("why") is None else {}
        )
        named_as = expr
        if m := re.fullmatch(r"TO_DECIMAL_(\d+)\(.*\)", expr):
            # A double's cast to a decimal: the precision is the cast's
            # around it, `DECIMAL_p_s(TO_DECIMAL_s(x))`.
            outer = re.compile(rf"DECIMAL_(\d+)_{m[1]}\({re.escape(expr)}\)")
            if found := next((x for i in raw if (x := outer.search(i["expr"]))), None):
                named_as = found[0]
        user = shown(named_as, kind in ("SUM overflow", INFINITE))
        fallback = None
        # The inference does not reach the columns (a window's value, a cast):
        # bounds on the columns the expression names, if a proof confirms
        # them (#688).
        guessed = (
            guess(user) if error and not constant and bound and bound.get("why") and user else {}
        )
        if guessed:
            code, fallback = guessed, text
            text = (
                "bound the columns it reads: state "
                + " and ".join(
                    f"{', '.join(f'`{label(c)}`' for c in cs)} in the requires of {t!r}"
                    for t, cs in guessed.items()
                )
                + " (or tighter bounds your data keeps)"
            )
        out.append(
            Issue(
                kind,
                expr,
                # Lean keeps the IEEE value of an overflow to ±∞ (#575), and
                # a report counts it as a `SUM` overflow: assumed with
                # `infer`, an error without.
                error,
                text,
                column(expr) if kind == "SUM overflow" else None,
                constant,
                any(i.get("under_and_or", False) for i in members),
                tuple(label(c) for cs in code.values() for c in cs) if not fallback else (),
                user,
                # The inference's preconditions, as data; a guess is not one.
                [_needed(t, c, dialect) for t, cs in code.items() for c in cs]
                if error and not fallback
                else [],
                hint_needs={t: list(cs) for t, cs in code.items()} if error else {},
                unconfirmed=fallback,
            )
        )
    return out


DIVISION_HINT = (
    "Ibis `//` floors and `%` truncates, so `({a} // {b}) * {b} + {a} % {b} == {a}` "
    "fails for negative {a}: bound {a} below by 0 in `requires`, or write the plan in SQL, "
    "where `//` truncates (guide: 'Integer division in Ibis and SQL')"
)


def division_hints(transform: ir.Table) -> list[str]:
    """For each integer `a // b` and `a % b` the Ibis expression applies to the
    same operands: that the pair does not split `a` for negative values
    (#693)."""
    import ibis.expr.operations as ops

    node = transform.op()
    mods = {
        (m.left, m.right)
        for m in node.find(ops.Modulus)
        if isinstance(m, ops.Modulus) and m.dtype.is_integer()  # pyrefly: ignore
    }
    hints: list[str] = []
    for d in node.find(ops.FloorDivide):
        if isinstance(d, ops.FloorDivide) and d.dtype.is_integer() and (d.left, d.right) in mods:
            hint = DIVISION_HINT.format(a=_ibis_text(d.left), b=_ibis_text(d.right))
            if hint not in hints:
                hints.append(hint)
    return hints


def _ibis_text(node: Any) -> str:
    """An operand as the user wrote it, as far as it is a column or literal."""
    import ibis.expr.operations as ops

    if isinstance(node, ops.Field):
        return node.name
    if isinstance(node, ops.Literal):
        return str(node.value)
    return "the operand"


def rounding_hints(
    transform: ir.Table,
    ensures: Sequence[Condition],
    checked: Sequence[CheckedCondition],
    facts: Sequence[dict],
    dtypes: Mapping[str, Any],
) -> list[str]:
    """For each unproved comparison of a double column with a number that the
    column's proved bounds miss only by rounding (by at most `1e-6` of the
    number, #85): how much, and the `approx` that proves it."""
    import ibis.expr.operations as ops

    bounds = {}
    for f in facts:
        dtype, b = dtypes.get(f["name"]), f["abstract"].get("int")
        if dtype is not None and dtype.is_floating() and b is not None:
            bounds[f["name"]] = tuple(
                None if v is None else decode_double(int(v)) for v in (b["lo"], b["hi"])
            )
    hints = []
    for cond, c in zip(ensures, checked, strict=True):
        if c.proved or not isinstance(cond, Deferred):
            continue
        try:
            node = cond.resolve(transform).op()
        except Exception:  # noqa: BLE001 - only a hint
            continue
        if not isinstance(node, ops.Less | ops.LessEqual | ops.Greater | ops.GreaterEqual):
            continue
        col, lit = node.left, node.right
        if not (isinstance(col, ops.Field) and isinstance(lit, ops.Literal)):
            continue
        if not lit.dtype.is_numeric() or col.name not in bounds:
            continue
        k = float(lit.value)
        lo, hi = bounds[col.name]
        above = isinstance(node, ops.Less | ops.LessEqual)
        edge = hi if above else lo
        if edge is None or not math.isfinite(edge):
            continue
        excess = edge - k if above else k - edge
        if 0 < excess <= 1e-6 * max(1.0, abs(k)):
            hints.append(
                f"{c.label} holds up to rounding: {col.name} is proved within {excess:.3g} of "
                f"{k:g} (#85); state it as sv.approx({c.label})"
            )
    return hints


def _int_bounds(facts: Sequence[dict], dtypes: Mapping[str, Any]) -> dict:
    """The integer bounds of the integer output columns in the checker's `facts`."""
    out = {}
    for f in facts:
        dtype, b = dtypes.get(f["name"]), f["abstract"].get("int")
        if dtype is not None and dtype.is_integer() and b is not None:
            out[f["name"]] = tuple(None if v is None else int(v) for v in (b["lo"], b["hi"]))
    return out


def _origin(rel: Node, name: str) -> tuple[str, str] | None:
    """The base table and column that column `name` of relation `rel` passes
    on unchanged, if there is one."""
    if isinstance(rel, ops.UnboundTable | ops.DatabaseTable):
        return rel.name, name
    if isinstance(rel, ops.SelfReference):
        return _origin(rel.parent, name) if name in rel.parent.schema else None
    values = getattr(rel, "values", None)
    if isinstance(rel, ops.Aggregate):
        values = {**rel.groups, **rel.metrics}
    if values is not None:
        return _value_origin(values[name]) if name in values else None
    parent = getattr(rel, "parent", None)
    if parent is not None and name in parent.schema:
        return _origin(parent, name)
    return None


def _confirmed_ties(
    transform: ir.Table,
    requires: Mapping[str, Sequence[Condition]],
    report: Report,
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    params: list[str],
    inputs: Collection[str] | None,
    semantics: Semantics,
) -> dict[str, list[str]]:
    """`tie_keys`, where declaring them makes the result determined (#688):
    a key the checker cannot follow to the ORDER BY (through a join, say) is
    not suggested."""
    keys = tie_keys(transform)
    stated = {t: {label(c) for c in cs} for t, cs in requires.items()}
    keys = {
        t: [k for k in ks if k not in stated.get(t, set())]
        for t, ks in keys.items()
        if inputs is None or t in inputs
    }
    keys = {t: ks for t, ks in keys.items() if ks}
    if not keys:
        return {}
    widened = {t: list(cs) for t, cs in requires.items()}
    _merge(widened, report._inferred)
    for t, ks in keys.items():
        for k in ks:
            cols = re.fullmatch(r"unique\((.*)\)", k)
            if cols:
                widened.setdefault(t, []).append(unique(*cols[1].split(", ")))
    again = _infer_bounds(transform, widened, [], tables, 0, params, False, inputs, semantics)
    return keys if again.deterministic else {}


def tie_keys(expr: ir.Table) -> dict[str, list[str]]:
    """The `sv.unique(...)` per input table that leaves no ties in the
    ORDER BY of a window or of an ordered aggregate (`first`, `last`, …):
    its partition (or grouping) and order columns, as labels (#655)."""
    out: dict[str, list[str]] = {}

    def add(fields: Sequence[Any]) -> None:
        cols = [o for f in fields if (o := _value_origin(f)) is not None]
        tables = {t for t, _c in cols}
        if len(tables) != 1 or len(cols) != len(fields):
            return
        (t,) = tables
        lab = label(unique(*dict.fromkeys(c for _t, c in cols)))
        if lab not in out.setdefault(t, []):
            out[t].append(lab)

    def fields_of(values: Sequence[Any]) -> list[Any]:
        found: list[Any] = []
        for v in values:
            v = getattr(v, "expr", v)
            found += [f for f in v.find(ops.Field) if isinstance(f, ops.Field) and f not in found]
        return found

    for agg in expr.op().find(ops.Aggregate):
        if not isinstance(agg, ops.Aggregate):
            continue
        for metric in agg.metrics.values():
            order = getattr(metric, "order_by", None)
            if order:
                add(fields_of([*agg.groups.values(), *order]))
    for win in expr.op().find(ops.WindowFunction):
        if isinstance(win, ops.WindowFunction) and win.order_by:
            add(fields_of([*win.group_by, *win.order_by]))
    return out


def _input_columns(rel: Node, names: Sequence[str]) -> list[tuple[str, str]]:
    """The base table columns the output columns `names` of `rel` read:
    the column itself where it is passed on, else the columns its value
    reads that are passed on (`length(s)` reads `s`)."""
    out: list[tuple[str, str]] = []
    values = getattr(rel, "values", None)
    if isinstance(rel, ops.Aggregate):
        values = {**rel.groups, **rel.metrics}
    for name in names:
        if (o := _origin(rel, name)) is not None:
            found = [o]
        elif values is not None and name in values:
            fields = [f for f in values[name].find(ops.Field) if isinstance(f, ops.Field)]
            found = [o for f in fields if (o := _value_origin(f)) is not None]
        else:
            found = []
        out += [o for o in found if o not in out]
    return out


def _value_origin(value: Node) -> tuple[str, str] | None:
    """The base table and column a value is, if it is a column passed on
    unchanged."""
    if isinstance(value, ops.Field):
        return _origin(value.rel, value.name)
    return None


#: The bound a SUM hint proposes for an unbounded side of a column.
SUM_BOUND = 1_000_000_000


#: What a report suggests for an error under `AND`/`OR` (#604, D19).
AND_OR_HINT = (
    "`{}` is inside an AND or OR you wrote (`{}`), and DuckDB and Polars evaluate "
    "both operands on every row, so a guard in the other operand does not keep it "
    "from raising. Guard the operation itself with {} (a boolean CASE is "
    "evaluated whole, as AND and OR are), or state the guard as a precondition"
)


_IDENT = re.compile(r"(?<![\w.'\"])([A-Za-z_]\w*)\b(?!\s*\()")


def _user_and_or(transform: Transform) -> list[set[str]]:
    """The columns each AND or OR the user wrote reads: Ibis's `&`, `|`
    (not those the producer writes, such as in a floor division), or SQL's
    `AND`, `OR` (every column, as the SQL is not walked)."""
    if isinstance(transform, str):
        return [set[str]()] if re.search(r"\b(AND|OR)\b", transform, re.IGNORECASE) else []
    found: list[set[str]] = []
    for op in transform.op().find((ops.And, ops.Or, ops.Xor)):
        found.append({str(f.name) for f in op.find(ops.Field)})
    # Ibis splits a filter's `&` into its predicates.
    for op in transform.op().find(ops.Filter):
        if len(op.predicates) > 1:
            found.append({str(f.name) for p in op.predicates for f in p.find(ops.Field)})
    return found


def and_or_hints(issues: Sequence[Issue], transform: Transform | None = None) -> list[str]:
    """`AND_OR_HINT` for each error under an `AND`/`OR` the user wrote, once
    per expression (#688): the checker also counts those the producer
    writes."""
    dialect = "sql" if isinstance(transform, str) else "ibis"
    held = _user_and_or(transform) if transform is not None else [set()]
    seen = []
    for i in issues:
        e = i.shown or i.expr
        if not (i.error and i.under_and_or) or e in seen:
            continue
        cols = set(_IDENT.findall(e))
        if any(not reads or cols <= reads for reads in held):
            seen.append(e)
    return [_and_or_hint(e, dialect) for e in seen]


def _and_or_hint(e: str, dialect: str = "ibis") -> str:
    """`AND_OR_HINT` for one operation, with the guard written out where it
    is a division: `ibis.cases((_.qty != 0, _.total // _.qty))`."""
    m = re.fullmatch(r"(\w+) (//|/|%) (\w+)", e)
    op = "&` or `|" if dialect == "ibis" else "AND` or `OR"
    if m and not m[3].isdigit():
        a, div, b = m.groups()
        guard = (
            f"`ibis.cases((_.{b} != 0, _.{a} {div} _.{b}))`"
            if dialect == "ibis"
            else f"`CASE WHEN {b} <> 0 THEN {a} {div} {b} END`"
        )
    else:
        guard = (
            f"`ibis.cases((<guard>, {e}))`"
            if dialect == "ibis"
            else f"`CASE WHEN <guard> THEN {e} END`"
        )
    return AND_OR_HINT.format(e, op, guard)


def overflow_hints(
    transform: ir.Table, requires: Mapping[str, Sequence[Condition]], report: Report
) -> list[str]:
    """The bounds to add to `requires` for the overflows `report` names (#379):
    lower and upper bounds on each truncated timestamp or date column, and for
    an integer `SUM` that is checked while the job runs, a bound on the
    column it adds up, with the largest group whose sum then fits 64 bits."""
    hints: list[str] = []
    # An overflow with its own hint (`infer_bounds`) has its exact bounds.
    if any(i.kind == "overflow" and _truncates(i.expr) and not i.hint for i in report.errors):
        kinds = (ops.TimestampTruncate, ops.DateTruncate, ops.TimestampBucket)
        for op in transform.op().find(kinds):
            if (origin := _value_origin(op.arg)) is None:  # type: ignore[attr-defined]
                continue
            table, col = origin
            ctor = "date" if op.arg.dtype.is_date() else "datetime"  # type: ignore[attr-defined]
            hints.append(
                f"{TRUNC_HINT} `{col}` in `requires` of {table}: truncating a value near the "
                f"ends of the timestamp range overflows. For example `_.{col} >= {ctor}(2000, "
                f"1, 1)` and `_.{col} < {ctor}(2100, 1, 1)`"
            )
    if any(_sum(i) for i in report.errors):
        for op in transform.op().find(ops.Sum):
            if (hint := _sum_hint(op, requires)) is not None:
                hints.append(hint)
    return list(dict.fromkeys(hints))


def _sum_column(transform: ir.Table | str, expr: str) -> str | None:
    """The column an integer `SUM` that Lean names `expr` (`$i`, its
    input's i-th column) adds up, named as `_sum_hint` names it, if exactly
    one `SUM` of the transformation matches."""
    if isinstance(transform, str) or not re.fullmatch(r"\$\d+", expr):
        return None
    names = set()
    for op in transform.op().find(ops.Sum):
        arg = op.arg  # type: ignore[attr-defined]
        rels = list(arg.relations)
        if not arg.dtype.is_integer() or len(rels) != 1 or not isinstance(arg, ops.Field):
            continue
        cols = rels[0].schema.names
        if arg.name not in cols or f"${cols.index(arg.name)}" != expr:
            continue
        origin = _value_origin(arg)
        names.add(origin[1] if origin else arg.name)
    return names.pop() if len(names) == 1 else None


def _sum_hint(op: Node, requires: Mapping[str, Sequence[Condition]]) -> str | None:
    """The hint for an integer `SUM`: what bounds its argument, and the
    largest group whose sum fits 64 bits."""
    arg = op.arg  # type: ignore[attr-defined]
    rels = list(arg.relations)
    if not arg.dtype.is_integer() or len(rels) != 1:
        return None
    origin = _value_origin(arg)
    what = f"`{origin[1]}`" if origin else f"`{arg.name}`"
    sub = rels[0].to_expr().select(x=arg.to_expr())
    leaves = leaf_tables(sub)
    known = {
        t: [c for c in cs if not isinstance(c, References)]
        for t, cs in requires.items()
        if t in leaves
    }
    report = verify(sub, requires=known, counterexamples=0, on_inferred="off")
    lo, hi = report._bounds.get("x", (None, None))
    # A BIGINT's own range bounds nothing: any two of its values may overflow.
    lo = None if lo is None or lo <= -(2**63) else lo
    hi = None if hi is None or hi >= 2**63 - 1 else hi
    where = f"`requires` of {origin[0]}" if origin else f"`requires` (on the columns of {what})"

    def capped(n: int) -> str:
        """The row cap that proves the sum fits (#219)."""
        return (
            f"`sv.max_rows({n:_})` in {where} proves it, and so does "
            f"`sv.rows_per(<grouping columns>, at_most={n:_})`; without a row bound, the job "
            "checks the sum as it runs"
        )

    if lo is not None and hi is not None:
        largest = max(abs(lo), abs(hi))
        if largest == 0:
            return None
        rows = (2**63 - 1) // largest
        if rows >= 2**63 - 1:
            # A group has fewer than 2^63 rows (`Rel.sumRows`, #437): the
            # sum fits, and Lean proves it.
            return None
        return (
            f"SUM of {what}: it is in [{lo}, {hi}], so a group's sum fits 64 bits for up to "
            f"{rows:,} rows; {capped(rows)}"
        )
    col = origin[1] if origin else "x"
    proposed = []
    if hi is None:
        proposed.append(f"`_.{col} <= {SUM_BOUND:_}`")
    if lo is None:
        proposed.append(f"`_.{col} >= {-SUM_BOUND:_}`")
    largest = max(SUM_BOUND, abs(lo or 0), abs(hi or 0))
    rows = (2**63 - 1) // largest
    return (
        f"SUM of {what}: bound it in {where}, for example {' and '.join(proposed)}; then a "
        f"group's sum fits 64 bits for up to {rows:,} rows, and {capped(rows)}"
    )


@dataclass(frozen=True)
class Fact:
    """What table metadata says about every row of a table, as a SQL
    condition, and where it comes from ("Delta constraint", "file stats @v3").
    The metadata is trusted; facts only discharge preconditions through Lean
    (`contract_sound` on the table itself), never by name."""

    condition: str
    source: str
    rows: int | None = None
    """For a row-count fact, at most this many rows; its `condition` is then
    `TRUE` (the record counts of a table format's files, #219)."""


SCHEMA = "schema"


# Metadata facts of tables read from a table format (`sverify.io`), keyed
# by backend identity and table name. Tables without an entry only have
# their preconditions checked on the data: an in-memory schema is not enforced.
# Each entry keeps a weak reference to its backend: a backend that is gone
# may leave its `id` to a new one, which must not inherit its facts.
_facts: dict[tuple[int, str], tuple[weakref.ref[Any], list[Fact]]] = {}


def register_facts(con: Connection, name: str, facts: Sequence[Fact] | None) -> None:
    """Record (or with None, forget) what metadata says about table `name`."""
    key = (id(con._ibis), name)
    if facts is None:
        _facts.pop(key, None)
    else:
        for k in [k for k, (ref, _) in _facts.items() if ref() is None]:
            del _facts[k]
        _facts[key] = (weakref.ref(con._ibis), list(facts))


def table_facts(table: ir.Table) -> list[Fact] | None:
    """Metadata facts of a base table, if it was read from a table format."""
    op = table.op()
    if not isinstance(op, ops.DatabaseTable):
        return None
    entry = _facts.get((id(op.source), op.name))
    if entry is None or entry[0]() is not op.source:
        return None
    return entry[1]


_proved_from: dict[tuple, frozenset[str]] = {}


def _prove_from(table: ir.Table, facts: Sequence[str], conds: Sequence[Condition]) -> set[str]:
    """Labels of `conds` that Lean proves about every row of `table` from its
    schema and `facts`. A fact the checker cannot read proves nothing."""
    name = table.op().name  # type: ignore[attr-defined]
    key = (name, str(table.schema()), tuple(facts), tuple(label(c) for c in conds))
    if key not in _proved_from:
        try:
            report = verify(
                table,
                requires={name: list(facts)},
                ensures=conds,
                counterexamples=0,
                on_inferred="off",
            )
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
    # A row cap from a row-count fact of metadata.
    counts = [(f.rows, f.source) for f in facts or [] if f.rows is not None]
    counted = {
        id(c): source
        for c in todo
        if isinstance(c, TableCondition)
        for source in [next((s for n, s in counts if c.capped_by(n)), None)]
        if source is not None
    }
    out += [Discharged(name, label(c), counted[id(c)]) for c in todo if id(c) in counted]
    todo = [c for c in todo if id(c) not in counted]
    if facts is not None:
        stages: dict[str, list[str]] = {SCHEMA: []}
        for f in facts:
            if f.rows is None:
                stages.setdefault(f.source, []).append(f.condition)
        assumed: list[str] = []
        for source, extra in stages.items():
            rowwise = [c for c in todo if not isinstance(c, TableCondition)]
            if not rowwise:
                break
            assumed += extra
            proved = _prove_from(table, assumed, rowwise)
            out += [
                Discharged(name, label(c), source, isinstance(c, Inferred))
                for c in rowwise
                if label(c) in proved
            ]
            todo = [c for c in todo if label(c) not in proved]
    for c in todo:
        if n := violations(table, c, engine):
            raise PreconditionError(
                f"{n} {what} violate {label(c)}",
                source=name,
                condition=c,
                rows=violating_rows(table, c),
            )
        out.append(Discharged(name, label(c), ON_DATA, isinstance(c, Inferred)))
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
    names both sides, for example "doubled needs (_.amount >= 0) (it may be
    FALSE on some rows) on 't'; not_null only guarantees _.amount.notnull()". With
    `on_unproved="check"` and a bound input, the precondition is checked on
    the data instead; with `on_unproved="warn"` it is a warning.

    Attributes:
        report: The `Report` of the failed proof of the link.
        consumer: The name of the transformation whose precondition failed.
        param: The parameter of `consumer` that received the input.
        producer: The name of the contracted transformation that produced it.
    """

    code = "composition_not_proved"

    def __init__(self, report: Report, consumer: str, param: str, producer: str, guarantees):
        self.report = report
        self.consumer, self.param, self.producer = consumer, param, producer
        needs = ", ".join(f"{c.label} ({c.why})" for c in report.unproved)
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
    merely warned about, instead of proved, and runtime-checked
    postconditions of contracted transformations upstream."""
    checked: list[Condition] = field(default_factory=list)
    """The postconditions `on_unproved="check"` checks on the result's data
    because they were not proved: on a bound result when it is built, and in
    an incremental view on every state (`IncrementalView.checked`)."""
    policies: Policies = field(default_factory=dict)
    """For each precondition in `external`, by table and label, the
    `on_violation` of every transform that states it (None: unset)."""


def _checked_links(prov: Provenance) -> list[str]:
    """A result's runtime-checked postconditions, as seen downstream: checked
    on its own rows, they are nothing a consumer's state is checked for."""
    return [f"{prov.transform.name}: {label(c)} was checked on data" for c in prov.checked]


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
    policies: Policies = field(default_factory=dict)


def _merge_policies(into: Policies, extra: Policies) -> None:
    for t, by_label in extra.items():
        have = into.setdefault(t, {})
        for lab, ps in by_label.items():
            have.setdefault(lab, set()).update(ps)


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
            _merge_policies(out.policies, prov.policies)
            out.unproved_links += prov.unproved_links + _checked_links(prov)
    return out


@dataclass
class ViewContract:
    """The contract of a (possibly composed) contracted expression, as seen by
    an incremental view: it `guarantees` its proved postconditions on every
    state whose base tables satisfy `requires`."""

    requires: dict[str, list[Condition]]
    guarantees: list[Condition]
    provenance: Provenance | None
    checked: list[Condition] = field(default_factory=list)
    """Postconditions that were not proved, which the view checks on every
    state (`on_unproved="check"`)."""
    not_null: list[str] = field(default_factory=list)
    """The columns the proved report shows never NULL (`Report.not_null`):
    they hold in every state, as `guarantees` do."""
    policies: Policies = field(default_factory=dict)
    """The `on_violation` the transforms set on each precondition in
    `requires` (`Provenance.policies`)."""


def view_contract(expr: ir.Table) -> ViewContract:
    """Collect the base-table preconditions of every contracted
    transformation inside `expr`. Refuses preconditions on derived inputs that
    were checked on data instead of proved: a view could not keep them true
    from base-table changes."""
    prov = _lookup(expr.op())
    if prov is not None:
        requires, unproved, policies = prov.external, prov.unproved_links, prov.policies
    else:
        inner = _abstract(expr)
        requires, unproved, policies = inner.external, inner.unproved_links, inner.policies
    if unproved:
        raise ValueError(
            "cannot maintain incrementally: conditions on derived inputs were "
            f"not proved ({'; '.join(unproved)})"
        )
    if per_key := [label(c) for cs in requires.values() for c in cs if isinstance(c, RowsPer)]:
        raise ValueError(
            "cannot maintain incrementally: batches are not checked against rows_per yet "
            f"(#219): {', '.join(per_key)}"
        )
    return ViewContract(
        {t: list(cs) for t, cs in requires.items()},
        list(prov.guarantees) if prov else [],
        prov,
        list(prov.checked) if prov else [],
        list(prov.report.not_null) if prov and prov.report.proved else [],
        {t: {lab: set(ps) for lab, ps in by.items()} for t, by in policies.items()},
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
        *,
        requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None = None,
        ensures: Sequence[Condition] = (),
        on_unproved: OnUnproved = "error",
        check_requires: bool = True,
        check_engine: Engine | None = None,
        semantics: Semantics = "reference",
        on_inferred: OnInferred = "error",
        on_violation: Policy | None = None,
    ):
        self.fn, self.ensures = fn, expand_keys(ensures)
        self.on_violation: Policy | None = check_policy(on_violation)
        """What a refresh does with a batch of a source that breaks this
        transform's preconditions (#184); None: the source's setting."""
        self.on_inferred = _checked_on_inferred(on_inferred)
        self.on_unproved, self.check_requires = on_unproved, check_requires
        self.semantics = _checked_semantics(semantics)
        self.check_engine = check_engine
        self.name: str = fn.__name__
        self.signature = inspect.signature(fn)
        self.requires: dict[str, Sequence[Condition]] = requires_by_input(
            requires, list(self.signature.parameters), "parameter", TypeError
        )
        self.report: Report | None = None
        """The `Report` of the proof of the postconditions in the last call,
        or None before the first call: the report of this transform, as a
        node's `report` is the node's."""
        self._counterexamples: int | None = None
        self._cache: dict[tuple, Report] = {}
        functools.update_wrapper(self, fn)

    @property
    def last_report(self) -> Report | None:
        """Deprecated: `report`."""
        warnings.warn(
            "ContractedTransform.last_report is deprecated; read .report",
            DeprecationWarning,
            stacklevel=2,
        )
        return self.report

    def to_substrait(
        self,
        format: Literal["json", "binary"] = "json",
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> str | bytes:
        """The verified plan of the last call, with its contract as
        metadata: `Report.to_substrait` of `report`. A call proves the
        contract for its inputs' schemas, so call the transform first, on
        tables, sources or nodes; `Node.to_substrait` exports a node.

        Args:
            format: `"json"` (protobuf JSON, a string) or `"binary"` (the
                serialized `substrait.Plan`).
            shims: What to do at a spec gap the proof depends on (see
                `Report.to_substrait`).

        Returns:
            The plan, as protobuf JSON or bytes.

        Raises:
            sverify.errors.ExportError: The transform has not been called
                yet, its report is not proved, or the plan has no
                conforming Substrait form that keeps the proof.
        """
        from sverify.substrait_export import ExportError

        if self.report is None:
            raise ExportError(
                f"{self.name} has not been called yet: call it on tables, sources or "
                "nodes first, which proves its contract for their schemas"
            )
        return self.report.to_substrait(format, shims=shims)

    def _verify(
        self,
        body: ir.Table,
        assumptions: Mapping[str, Sequence[Condition]],
        ensures,
        tag: str,
        inputs: Collection[str] = (),
        infer: bool = False,
    ) -> Report:
        """Prove `ensures` of `body`, inferring bounds on the tables in
        `inputs` with `infer` (`infer_bounds`)."""
        params = [
            p for p in body.op().find(ops.ScalarParameter) if isinstance(p, ops.ScalarParameter)
        ]
        if params:
            # Ibis's SQL compiler raises a bare KeyError on them (#440).
            names = ", ".join(f"ibis.param({p.dtype})" for p in params)
            name = getattr(self.fn, "__name__", "the transformation")
            raise TypeError(
                f"{name} uses {names}: a transformation does not bind "
                "parameters yet (#354). Prove it for given values with "
                "sv.verify(expr, params={param: value}), or write the values as "
                "ibis.literal(...)"
            )
        inputs = frozenset(inputs)
        budget = (
            default_counterexamples() if self._counterexamples is None else self._counterexamples
        )
        key = (
            tag,
            inputs,
            infer,
            self.on_inferred,
            self.semantics,
            ibis.to_sql(body, dialect="duckdb"),
            tuple(sorted((n, str(s)) for n, s in leaf_tables(body).items())),
            tuple(sorted((t, tuple(label(c) for c in cs)) for t, cs in assumptions.items())),
            tuple(label(c) for c in ensures),
            budget,
        )
        if key not in self._cache:
            self._cache[key] = infer_bounds(
                body,
                requires=assumptions,
                ensures=ensures,
                tables=None,
                counterexamples=budget,
                params=[],
                infer=infer,
                inputs=inputs,
                semantics=self.semantics,
                # Only the postconditions' proof needs the user's bounds; the
                # links' and conditions' proofs infer as before.
                on_inferred=self.on_inferred if tag == "ensures" else "ignore",
            )
        return self._cache[key]

    def _check_on_data(
        self, table: ir.Table, param: str, conds: Sequence[Condition], found: list[Discharged]
    ) -> bool:
        """Establish preconditions on a bound input, from its metadata where
        possible (`discharge`), adding how to `found`; False if it is not bound."""
        if not is_bound(table):
            return False
        found += discharge(
            table, param, conds, self.check_engine, table_facts(table), f"row(s) of {param}"
        )
        return True

    def _link(
        self,
        param: str,
        value: ir.Table,
        conds: list[Condition],
        found: list[Discharged],
        entry: Collected | None = None,
    ) -> _Abstraction:
        """Discharge this transformation's preconditions on a derived input by
        proving them from what produced it (assume-guarantee composition).
        Returns, as `assumptions`, what may be assumed about the input."""
        prov = _lookup(value.op())
        if prov is not None:
            inner = _Abstraction(
                prov.body,
                prov.assumptions,
                prov.external,
                list(prov.unproved_links) + _checked_links(prov),
                prov.policies,
            )
            known = list(prov.guarantees)
        else:
            # A plain Ibis expression guarantees nothing by itself, but its
            # obligations may still follow from its operations.
            inner, known = _abstract(value), []
        needed = [c for c in conds if label(c) not in {label(k) for k in known}]
        out = _Abstraction(
            value, {param: known + needed}, inner.external, inner.unproved_links, inner.policies
        )
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
                self._check_on_data(value, param, unproved, found)
            return out
        error = CompositionError(
            report, self.name, param, prov.transform.name, [label(c) for c in known]
        )
        if self.on_unproved == "warn":
            warnings.warn(UnprovedWarning(_warning_text(error), report), stacklevel=4)
        elif self.on_unproved == "check" and self._check_on_data(value, param, unproved, found):
            pass
        elif entry is not None:
            entry.links.append(error)
        else:
            raise error
        return out

    def _pipe_args(self, chained: Any, inputs: Mapping[str, Any]) -> tuple[tuple, dict[str, Any]]:
        """How `Node.pipe` passes the chained node and the keyword inputs:
        the chained node in the first parameter, the rest by keyword."""
        return _pipe.bind(self, chained, inputs)

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
                with `"check"` when the result is neither bound nor a
                node).
            PostconditionError: With `on_unproved="check"`, an unproved
                postcondition fails on the output data of a bound result. A
                node's are checked at every refresh instead
                (`sverify.Node.refresh`).
            TypeError: Sources or nodes are mixed with Ibis tables.
            ValueError: The node would read two tables of the same name.
        """
        if _hooks.wants_node(args, kwargs):
            return _hooks.nodes().derive(self, args, kwargs)
        return self._build(args, kwargs, node=False)

    def check(self, *args: Any, counterexamples: int | None = None, **kwargs: Any) -> Report:
        """Prove the contract for the input schemas, and return the report
        without raising and without reading data.

        `doubled.check(orders=schema)` is `doubled(orders)` on an unbound
        table of that schema: the postconditions are proved, the needed
        preconditions inferred, and the report kept in `report`. An
        unproved contract does not raise `VerificationError`, a bound table
        stands for its schema (its data is not read, so `requires` is not
        checked on it), and `on_unproved` does not apply. An editor, a test
        or a CI step reads the report (`Report.proved`, `Report.needed`).

        Args:
            *args: The inputs, positionally: Ibis tables, `ibis.Schema`s, or
                mappings from column name to type (`{"id": "int64"}`).
            counterexamples: Inputs tried per unproved postcondition for one
                that breaks it (`sverify.counterexample`); 0 skips the
                search. Default: `default_counterexamples()`, as a call uses.
            **kwargs: The inputs by parameter name, likewise.

        Returns:
            The `Report` of the proof.

        Raises:
            TypeError: The inputs do not match the function's parameters, or
                one is no table or schema (a source or a node: check the
                transform on its `schema` instead).
        """
        bound = self.signature.bind(*args, **kwargs)
        for name, value in bound.arguments.items():
            if isinstance(value, ir.Table):
                value = value.schema()
            if isinstance(value, Mapping) and not isinstance(value, ibis.Schema):
                value = ibis.schema(value)
            if not isinstance(value, ibis.Schema):
                raise TypeError(
                    f"{self.name}.check: {name} must be an Ibis table or a schema, "
                    f"not {type(value).__name__}"
                )
            bound.arguments[name] = ibis.table(value, name=name)
        before = self._counterexamples
        self._counterexamples = counterexamples
        try:
            self._build(bound.args, bound.kwargs, node=False, raise_unproved=False)
        except VerificationError as e:  # from a link of a composed input
            self.report = e.report
        finally:
            self._counterexamples = before
        assert self.report is not None
        return self.report

    def _build(
        self,
        args: Sequence[Any],
        kwargs: Mapping[str, Any],
        *,
        node: bool,
        raise_unproved: bool = True,
    ) -> ir.Table:
        """The result and its proof. A `node` result (`nodes.derive`, on
        placeholder tables) has its runtime-checked postconditions checked
        at every refresh instead of now."""
        inputs = self.signature.bind(*args, **kwargs).arguments
        found: list[Discharged] = []
        entry = None
        if (collected := COLLECTING.get()) is not None:
            entry = Collected(self, node)
            collected.append(entry)
        result = self.fn(*args, **kwargs)
        placeholders: dict[Node, tuple[str, list[Condition]]] = {}
        base: dict[str, list[Condition]] = {}
        bound_inputs: dict[str, tuple[str, ir.Table]] = {}
        # Placeholders of plain expressions (a memtable, a filtered table):
        # their preconditions are checked on the data like a base table's.
        plain: dict[str, tuple[str, ir.Table]] = {}
        external: dict[str, list[Condition]] = {}
        policies: Policies = {}
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
                bound_inputs.setdefault(op.name, (param, value))  # type: ignore[attr-defined]
                if self.check_requires:
                    self._check_on_data(value, param, conds, found)
                continue
            link = self._link(param, value, conds, found, entry)
            _merge(external, link.external)
            _merge_policies(policies, link.policies)
            unproved_links += link.unproved_links
            if op in placeholders:  # the same input under two parameters
                name, assumed = placeholders[op]
                _merge({name: assumed}, {name: link.assumptions[param]})
            else:
                prov = _lookup(op)
                name = _fresh(prov.transform.name if prov else param, taken)
                placeholders[op] = (name, link.assumptions[param])
                if prov is None:
                    plain[name] = (param, value)
        abstraction = _abstract(result, placeholders, taken)
        assumptions = {**abstraction.assumptions}
        _merge(assumptions, base)
        report = self.report = self._verify(
            abstraction.body,
            assumptions,
            self.ensures,
            "ensures",
            {*base, *plain},
            self.on_inferred != "off",
        )
        # Inferred bounds on the inputs are preconditions like the rest:
        # checked on the data (or proved from metadata) and passed on,
        # before any check on the output reads them.
        for t, conds in report._inferred.items():
            _merge(assumptions, {t: conds})
            if t in plain:
                param, value = plain[t]
                unproved_links += [f"{self.name}: {label(c)} on {param}" for c in conds]
            else:
                _merge(base, {t: conds})
                param, value = bound_inputs[t]
            if self.check_requires:
                self._check_on_data(value, param, conds, found)
        if found:
            # The report may be cached and shared by calls: this call's copy.
            report = self.report = replace(report, preconditions=found)
        checked: list[Condition] = []
        if not report.proved and raise_unproved:
            # Runtime errors cannot be checked on the data beforehand: in
            # "check" mode the engine raises them if they happen.
            if self.on_unproved == "check" and (node or is_bound(result)):
                unproved = {c.label for c in report.unproved}
                checked = [c for c in self.ensures if label(c) in unproved]
                report = self.report = _marked_checked(report)
                for c in [] if node else checked:
                    if n := violations(result, c, self.check_engine):
                        raise PostconditionError(f"{n} output row(s) violate {label(c)}")
            elif entry is not None:
                pass  # collected: the caller reads the report
            elif self.on_unproved == "warn":
                error = VerificationError(report)
                warnings.warn(UnprovedWarning(_warning_text(error), report), stacklevel=3)
            else:
                raise VerificationError(report)
        if entry is not None:
            entry.report = report
            entry.params = {t: p for t, (p, _) in {**bound_inputs, **plain}.items()}
        _merge(external, abstraction.external)
        _merge(external, base)
        _merge_policies(policies, abstraction.policies)
        _merge_policies(
            policies,
            {t: {label(c): {self.on_violation} for c in cs} for t, cs in base.items()},
        )
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
                checked=checked,
                policies=policies,
            ),
        )
        return result


def _marked_checked(report: Report) -> Report:
    """`report` (cached, so left as it is) with its unproved postconditions
    marked as checked on data."""
    ensures = [c if c.proved else replace(c, checked=True) for c in report.ensures]
    return replace(report, ensures=ensures)


def transform(
    requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None = None,
    ensures: Sequence[Condition] = (),
    *,
    on_unproved: OnUnproved | Literal["runtime"] = "error",
    check_requires: bool = True,
    check_engine: Engine | None = None,
    semantics: Semantics = "reference",
    on_inferred: OnInferred = "error",
    on_violation: Policy | None = None,
) -> Callable[[Callable[..., ir.Table]], ContractedTransform]:
    """Decorate a function from Ibis tables to an Ibis table with a contract.

    `requires` maps parameter names to conditions on that input. On each call
    the postconditions are proved (cached per input schema and expression) and
    the report is kept in `.report`; see the module docstring. With
    `on_unproved="check"`, unproved postconditions are checked on the output
    data instead: on inputs bound to a connection, when the transform is
    called; on a node, at every refresh, on the rows the batch inserts, before
    its sink commits. The report marks them `checked`. `check_engine` says
    where those checks on data run (see the module docstring).

    Piped from a source (`sverify.io`) or a node, `orders.pipe(doubled)`, or
    called on one, `doubled(orders)`, the transform builds a `sverify.Node`
    instead of an Ibis expression: transforms compose over sources,
    `.write(sink)` stores a result, and `refresh` keeps it up to date (see
    `sverify.Node`). `Node.pipe` also takes a plain function, which is a
    transform with no contract.

    Args:
        requires: Preconditions, as a mapping from parameter name to
            conditions on that input (or, for a function of one table, a
            list of its conditions): Ibis expressions (`_.amount >= 0`),
            functions of the table, SQL snippets (`"amount >= 0"`), `unique`
            or `references`. Default: none.
        ensures: Postconditions on the result, in the same forms (but not
            `references`). Default: none, which still rules out runtime
            errors.
        on_unproved: What happens when a postcondition, or a precondition on
            another contracted transformation's result, is not proved:
            `"error"` (the default) raises; `"check"` checks a postcondition
            on the output data instead (bound inputs, or a node at every
            refresh) and a precondition on a bound input's data; `"warn"`
            emits a warning and returns the result, and a node's refreshes
            run it unverified, each with an `UnverifiedRunWarning`
            (`refresh(unverified=True)`). `"runtime"` is a deprecated
            spelling of `"check"`.
        check_requires: Whether to check preconditions on the data of bound
            inputs at call time. Default True. False with an
            `on_violation` other than `"error"` raises `ValueError`: that
            setting acts on those checks.
        check_engine: Where checks on data run: `"duckdb"` or `"polars"` (or
            the optional `"datafusion"`) run each condition's plan as Lean
            wrote it; None
            (the default) runs them through Ibis on the inputs' connection.
            `refresh(engine=)` says where a node's plan runs.
        semantics: What the contract's SQL conditions mean in its proofs,
            as `verify`'s: `"reference"` (the default) or `"duckdb"`.
        on_inferred: What a precondition sverify infers does, as
            `verify`'s. sverify infers the bounds it needs (`amount * 2` on
            BIGINT needs `_.amount < 2**62`). `"error"` (the default): the
            contract is not proved until `requires` states it or the
            transformation no longer needs it (`Report.needed`). `"warn"`:
            it is assumed and checked on the data or proved from table
            metadata, with an `sverify.errors.InferredWarning`. `"ignore"`:
            the same without the warning. `"off"`: nothing is inferred or
            assumed, so an integer `SUM` that may leave 64 bits is an error
            too, which the other values check on the data while the job
            runs (`Report.assumed`). `"silent"` is a deprecated spelling of
            `"ignore"`.
        on_violation: What a refresh does with a batch of a source that
            breaks one of these preconditions, inferred ones included
            (#184): `"error"` raises `PreconditionError`; `"quarantine"`
            sets the offending rows aside with the reason, in the node's
            quarantine table, and the rest flows; `"hold"` commits nothing
            for the batch and holds the node at its versions until a later
            version of the source meets the preconditions. Default None:
            the source's `on_violation`, else `"error"`. Where two
            transforms state the same condition, the stricter holds.

    Returns:
        A decorator that turns the function into a `ContractedTransform`.

    Raises:
        TypeError: When decorating, if `requires` names a parameter the
            function does not have. Calls raise `PreconditionError`,
            `CompositionError`, `VerificationError` or `PostconditionError`
            from `sverify.errors` (see `ContractedTransform.__call__`).

    Examples:
        A contract that holds, on a source, and what the checker worked out about
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

        big = orders.pipe(doubled)  # a Node, proved here (as doubled(orders))
        doubled.report.proved  # True
        doubled.report.facts["doubled"]  # 'an integer ≥ 22'
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

        big.pipe(plus_one)  # proved from what doubled guarantees

        @sv.transform(requires={"t": [_.doubled >= 100]})
        def huge(t):
            return t

        try:
            big.pipe(huge)
        except CompositionError as e:
            print(str(e).split(";")[0])
        # huge needs (_.doubled >= 100) (it may be FALSE on some rows) on 't'
        ```

        A postcondition that does not follow is refused:

        ```python
        from sverify.errors import VerificationError

        @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
        def total(orders):
            return orders.select(orders.id, total=orders.amount + 1)

        try:
            orders.pipe(total)
        except VerificationError as e:
            print(str(e).splitlines()[0])
        # could not prove: (_.total > 5) (it may be FALSE on some rows)
        ```
    """
    on_inferred = _checked_on_inferred(on_inferred)
    on_unproved = _checked_on_unproved(on_unproved)
    check_policy(on_violation)
    if not check_requires and on_violation not in (None, "error"):
        raise ValueError(
            f"on_violation={on_violation!r} acts on the checks of the preconditions on the "
            "data, which check_requires=False turns off"
        )
    return lambda fn: ContractedTransform(
        fn,
        requires=requires,
        ensures=ensures,
        on_unproved=on_unproved,
        check_requires=check_requires,
        check_engine=check_engine,
        semantics=semantics,
        on_inferred=on_inferred,
        on_violation=on_violation,
    )
