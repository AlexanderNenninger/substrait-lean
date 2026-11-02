"""Test sverify transforms and their contracts with pytest.

    import sverify as sv
    from sverify.testing import assert_contract, assert_engines_agree, cases, source

    def test_paid():
        orders = source([(1, 30), (2, 5)], {"id": "int64", "amount": "int64"}, name="orders")
        node = orders.pipe(paid)
        assert_contract(node)                                   # proved
        assert_contract(node, data={"orders": [(1, 30), (3, 50)]}, expected=[(1, 30), (3, 50)])
        assert_engines_agree(node, {"orders": [(1, 30), (2, 5)]})

* `assert_contract` asserts that a node's contract is proved, and with
  `data=` checks it on those rows: the preconditions hold on them, the
  output meets the postconditions, and with `expected=` it is those rows
  (with a diff when it is not).
* `assert_engines_agree` runs a node on every installed engine
  (`installed_engines`) and asserts that they give the same rows.
* `cases` is a Hypothesis strategy of input tables meeting a node's
  preconditions, for property tests of the code around it
  (`pip install 'sverify[testing]'`).
* `source` makes an in-memory source (`sverify.io.StaticSource`) from rows.

Installing sverify registers a pytest plugin (`sverify.pytest_plugin`) with
the fixtures `sv_engine`, which runs a test once per installed engine, and
`sv_source`, which is `source`.

The other functions here (`inline_tables`, `lean_rows`, `duckdb_rows`, …)
are internal, for sverify's own differential tests against Lean's semantics,
and may change in any release: `inline_tables` replaces each named-table read
by a Substrait virtual table holding given rows (integers, strings, booleans,
timestamps, dates, doubles, decimals and NULLs); `lean_rows` evaluates the plan with
`Rel.eval` via `substrait-check` (`lean_values` also reads printed doubles);
`duckdb_rows` runs it as SQL on DuckDB.
"""

from __future__ import annotations

import base64
import datetime as dt
import importlib.util
import json
import math
import re
import subprocess
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from decimal import ROUND_HALF_UP, Decimal
from typing import TYPE_CHECKING, Any, overload

import ibis
import pyarrow as pa

from sverify import counterexample
from sverify.contracts import (
    Condition,
    References,
    TableCondition,
    Unique,
    _lookup,
    condition_query,
    label,
    resolve,
)
from sverify.engine import (
    ENGINES,
    Connection,
    connect,
    plain_schema,
    plan_json,
    quote,
    run_checker,
    run_plan,
)
from sverify.incremental import StaticSource, arrow_rows
from sverify.nodes import Node, _Derived

if TYPE_CHECKING:
    from hypothesis.strategies import SearchStrategy

__all__ = [
    "assert_contract",
    "assert_engines_agree",
    "cases",
    "installed_engines",
    "source",
]

EPOCH = dt.datetime(1970, 1, 1)


def decimal_literal(v: Decimal, precision: int = 38, scale: int | None = None) -> dict:
    """A Substrait decimal literal: the unscaled integer, 16 bytes little-endian.
    Without a `scale`, the value's own; with one, rounded half away from zero."""
    if scale is None:
        exponent = v.as_tuple().exponent
        scale = max(0, -exponent) if isinstance(exponent, int) else 0
    unscaled = int(v.scaleb(scale).to_integral_value(rounding=ROUND_HALF_UP))
    value = base64.b64encode(unscaled.to_bytes(16, "little", signed=True)).decode()
    return {"literal": {"decimal": {"value": value, "precision": precision, "scale": scale}}}


def literal(v: object) -> dict:
    if isinstance(v, Decimal):
        return decimal_literal(v)
    if v is None:
        return {"literal": {"null": {"i64": {}}}}
    if isinstance(v, bool):
        return {"literal": {"boolean": v}}
    if isinstance(v, int):
        return {"literal": {"i64": str(v)}}
    if isinstance(v, str):
        return {"literal": {"string": v}}
    if isinstance(v, dt.datetime):
        micros = (v - EPOCH) // dt.timedelta(microseconds=1)
        return {"literal": {"precisionTimestamp": {"precision": 6, "value": str(micros)}}}
    if isinstance(v, dt.date):
        return {"literal": {"date": (v - EPOCH.date()).days}}
    if isinstance(v, dt.time):
        micros = ((v.hour * 60 + v.minute) * 60 + v.second) * 1_000_000 + v.microsecond
        return {"literal": {"precisionTime": {"precision": 6, "value": str(micros)}}}
    if isinstance(v, float):
        # The model's one zero and one NaN: -0.0 is 0.0, a negative NaN is NaN.
        text = "NaN" if math.isnan(v) else "Infinity" if v == math.inf else "-Infinity"
        return {"literal": {"fp64": v + 0.0 if math.isfinite(v) else text}}
    if isinstance(v, list):
        # Elements are literals without the `literal` key.
        if not v:
            return {"literal": {"emptyList": {"type": {"i64": {}}}}}
        return {"literal": {"list": {"values": [literal(x)["literal"] for x in v]}}}
    if isinstance(v, dict):
        # A struct is its fields, in order (`docs/nested-values.md`).
        return {"literal": {"struct": {"fields": [literal(x)["literal"] for x in v.values()]}}}
    raise TypeError(f"no literal for {v!r}")


def inline_tables(plan: dict, rows: Mapping[str, list[tuple]]) -> dict:
    """Replace the reads of the tables in `rows` by virtual tables (in place)."""

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                name = ".".join(node.pop("namedTable")["names"])
                # A decimal takes its column's type (`baseSchema`).
                types = node.get("baseSchema", {}).get("struct", {}).get("types", [])
                decs = [t.get("decimal") if isinstance(t, dict) else None for t in types]

                def cell(i: int, v: object) -> dict:
                    d = decs[i] if i < len(decs) else None
                    if isinstance(v, Decimal) and d is not None:
                        return decimal_literal(v, d.get("precision", 38), d.get("scale", 0))
                    return literal(v)

                exprs = [{"fields": [cell(i, v) for i, v in enumerate(row)]} for row in rows[name]]
                node["virtualTable"] = {"expressions": exprs}
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return plan


def _checked(plan_json: str) -> str:
    code, out, err = run_checker((), plan_json)
    if code != 0:
        raise subprocess.CalledProcessError(code, "substrait-check", out, err)
    return out


def lean_rows(plan_json: str) -> list[tuple]:
    """The rows `Rel.eval` gives for a plan with only virtual tables, in
    Lean's order. Doubles, timestamps and dates come back as their integer
    codes (`SubstraitLean/Float.lean`); doubles are refused."""
    out = _checked(plan_json)
    return parse_rows(out)


def lean_values(plan_json: str) -> list[tuple]:
    """Like `lean_rows`, but reads doubles too, which Lean prints with six
    decimals and a `d` (so only approximately)."""
    out = _checked(plan_json)
    return parse_rows(out, doubles=True)


_TOKEN = re.compile(r'\s*(NULL|true|false|"(?:[^"\\]|\\.)*"|\[|\]|,|[^,\[\]]+)')
_ESCAPE = re.compile(r"\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)")


def _unquote(s: str) -> str:
    """A string in Lean's quotes (`String.quote`, which escapes with `\\x..`)."""

    def char(m: re.Match[str]) -> str:
        e = m.group(1)
        if e[0] == "x":
            return chr(int(e[1:], 16))
        if e[0] == "u":
            return chr(int(e[2:-1], 16))
        return {"n": "\n", "t": "\t", "r": "\r"}.get(e, e)

    return _ESCAPE.sub(char, s[1:-1])


def _value(x: str, doubles: bool) -> object:
    if x == "NULL":
        return None
    if x in ("true", "false"):
        return x == "true"
    if x.startswith('"'):
        return _unquote(x)
    if re.fullmatch(r"-?\d+", x):
        return int(x)
    # A decimal, as `Main.decimalString` prints it.
    if re.fullmatch(r"-?\d+\.\d+", x):
        return Decimal(x)
    if doubles and x.endswith("d"):
        return float(x[:-1])
    raise ValueError(f"cannot read {x!r} (a double?) from Lean's output")


def parse_row(text: str, doubles: bool = False) -> tuple:
    """One row as `Row.render` prints it: `(v, …)`, lists as `[v, …]`."""
    tokens = [m.group(1) for m in _TOKEN.finditer(text.strip()[1:-1])]
    pos = 0

    def items(close: str | None) -> list[object]:
        nonlocal pos
        out: list[object] = []
        while pos < len(tokens) and tokens[pos] != close:
            t = tokens[pos]
            pos += 1
            if t == ",":
                continue
            if t == "[":
                out.append(items("]"))
                pos += 1  # the "]"
            else:
                out.append(_value(t.strip(), doubles))
        return out

    return tuple(items(None))


def parse_rows(output: str, doubles: bool = False) -> list[tuple]:
    """The rows section of `substrait-check` output (`renderCell` in `Main.lean`)."""
    rows = []
    for line in output.split("rows (")[1].splitlines()[1:]:
        if not line.startswith("  ("):
            break
        rows.append(parse_row(line, doubles))
    return rows


def duckdb_rows(plan_json: str, tables: Mapping[str, pa.Table] | None = None) -> list[tuple]:
    """Rows of the plan's SQL on a fresh DuckDB database holding `tables`."""
    from sverify import duckdb_engine

    return arrow_rows(duckdb_engine.run(plan_json, tables or {}))


def canonical(rows: Iterable[tuple]) -> list[str]:
    """A bag of rows in a canonical order (NULLs and NaN compare as text)."""
    return sorted(map(repr, rows))


# -- for users' tests ----------------------------------------------------------

type Rows = pa.Table | Sequence[Mapping[str, Any]] | Sequence[tuple]
"""A table's rows: an Arrow table, dicts by column name, or tuples in the
schema's column order."""

_EXTRAS = {"duckdb": (), "polars": ("polars", "numpy"), "datafusion": ("datafusion",)}


def installed_engines() -> tuple[str, ...]:
    """The engines of `sverify.engines.ENGINES` that can run here: DuckDB
    always, Polars and DataFusion when their extras are installed.

    Returns:
        Engine names, in the order of `ENGINES`.
    """
    return tuple(e for e in ENGINES if all(importlib.util.find_spec(m) for m in _EXTRAS[e]))


def _arrow_schema(schema: Any) -> pa.Schema:
    if isinstance(schema, pa.Schema):
        return schema
    if isinstance(schema, ibis.Schema):
        return schema.to_pyarrow()
    return ibis.schema(schema).to_pyarrow()


def _arrow(rows: Rows, schema: pa.Schema) -> pa.Table:
    if isinstance(rows, pa.Table):
        return rows.select(schema.names).cast(schema)
    dicts = [
        dict(r) if isinstance(r, Mapping) else dict(zip(schema.names, r, strict=True)) for r in rows
    ]
    return pa.Table.from_pylist(dicts, schema=schema)


def source(
    rows: Rows, schema: Any = None, *, name: str = "table", version: int = 0
) -> StaticSource:
    """An in-memory source (`sverify.io.StaticSource`) holding `rows`.

    The `sv_source` fixture of sverify's pytest plugin is this function.

    Args:
        rows: The rows: an Arrow table, dicts by column name, or tuples in
            the schema's column order.
        schema: The columns, as anything `ibis.schema` accepts (such as
            `{"id": "!int64", "amount": "int64"}`, where `!` is NOT NULL),
            an Ibis schema or an Arrow schema. Optional for an Arrow table.
        name: The table's name in the plans that read it. Default:
            `"table"`.
        version: The source's version. Default: 0.

    Returns:
        A `StaticSource`.

    Raises:
        TypeError: No schema is given for rows that are not an Arrow table.
    """
    if schema is None:
        if not isinstance(rows, pa.Table):
            raise TypeError("source() needs a schema unless the rows are an Arrow table")
        return StaticSource(rows, version, name=name)
    return StaticSource(_arrow(rows, _arrow_schema(schema)), version, name=name)


def _node(node: Any) -> Node:
    if not isinstance(node, Node):
        raise TypeError(
            f"expected a sverify.Node (a source piped into a transform), got {type(node).__name__}"
        )
    return node


def _requirements(node: Node, leaves: Sequence[Node]) -> dict[str, list[Condition]]:
    """What the node's stage assumes about each table it reads: the
    preconditions on its sources, and what a stored node guarantees."""
    out: dict[str, list[Condition]] = {leaf.name: [] for leaf in leaves}
    prov = _lookup(node._query()._expr.op())
    extra = [(t, cs) for t, cs in (prov.external if prov else {}).items() if t in out]
    for leaf in leaves:
        if (p := _lookup(leaf._expr.op())) is not None:
            extra.append((leaf.name, p.guarantees))
    for t, cs in extra:
        for c in cs:
            if label(c) not in {label(o) for o in out[t]}:
                out[t].append(c)
    return out


def _norm(v: object) -> object:
    """A value compared as a bag element: doubles approximately, with one
    zero and one NaN."""
    if isinstance(v, bool):
        return ("bool", v)
    if isinstance(v, float):
        return "NaN" if math.isnan(v) else float(f"{v + 0.0:.12g}")
    if isinstance(v, list | tuple):
        return tuple(map(_norm, v))
    if isinstance(v, dict):
        return tuple((k, _norm(x)) for k, x in v.items())
    return v


def _violating(con: Connection, name: str, cond: Condition) -> list[dict]:
    """The rows of table `name` where `cond` is not TRUE; for `unique`, every
    row whose key repeats."""
    rows = con.arrow[name].to_pylist()
    if isinstance(cond, Unique):
        keys = Counter(_norm(tuple(r[c] for c in cond.cols)) for r in rows)
        return [r for r in rows if keys[_norm(tuple(r[c] for c in cond.cols))] > 1]
    if isinstance(cond, References):
        present = {_norm(r[cond.other]) for r in con.arrow[cond.table].to_pylist()}
        return [r for r in rows if r[cond.col] is not None and _norm(r[cond.col]) not in present]
    if isinstance(cond, str):
        cur = con.ibis.raw_sql(f"SELECT * FROM {quote(name)} WHERE NOT coalesce(({cond}), FALSE)")
        cols = [d[0] for d in cur.description]
        return [dict(zip(cols, r, strict=True)) for r in cur.fetchall()]
    t = con.table(name)
    bad: Any = t.filter(~resolve(cond, t).fill_null(ibis.literal(False)))
    return bad.to_pyarrow().to_pylist()


def _listed(rows: Sequence[object], limit: int = 10) -> list[str]:
    lines = [f"    {r}" for r in rows[:limit]]
    if len(rows) > limit:
        lines.append(f"    … and {len(rows) - limit} more")
    return lines


def _connection(node: Node, data: Mapping[str, Rows]) -> Connection:
    """A connection holding `data` as the tables the node's stage reads,
    after checking that they meet what the stage assumes."""
    leaves = node._leaves()
    names = [leaf.name for leaf in leaves]
    missing = [n for n in names if n not in data]
    unknown = [n for n in data if n not in names]
    if missing or unknown:
        raise ValueError(
            f"data for {node.name} needs the tables {names}"
            + (f"; missing {missing}" if missing else "")
            + (f"; not read: {unknown}" if unknown else "")
        )
    con = connect()
    for leaf in leaves:
        con.put(leaf.name, _arrow(data[leaf.name], plain_schema(leaf.schema.to_pyarrow())))
    problems = []
    for t, conds in _requirements(node, leaves).items():
        for c in conds:
            if bad := _violating(con, t, c):
                problems += [f"  {len(bad)} row(s) of {t} violate {label(c)}:", *_listed(bad)]
    if problems:
        raise AssertionError(
            f"the test data does not meet what {node.name} requires:\n" + "\n".join(problems)
        )
    return con


def _output(con: Connection, node: Node, engine: str) -> tuple[pa.Table, list[str]]:
    """The node's output on `engine`, and the postconditions it violates."""
    out = run_plan(con, node.plan, engine)
    query = node._query()
    if not isinstance(query, _Derived):
        return out, []
    name = "__sverify_output"
    con.put(name, out)
    problems = []
    for c in query.transform.ensures:
        if bad := _violating(con, name, c):
            problems += [f"  {len(bad)} output row(s) violate {label(c)}:", *_listed(bad)]
    con.drop(name)
    return out, problems


def _diff(got: pa.Table, expected: Rows) -> list[str]:
    """The rows that differ between `got` and `expected`, as bags."""
    names = got.column_names
    want = (
        expected.to_pylist()
        if isinstance(expected, pa.Table)
        else [
            dict(r) if isinstance(r, Mapping) else dict(zip(names, r, strict=True))
            for r in expected
        ]
    )
    have = got.to_pylist()

    def key(r: Mapping[str, Any]) -> object:
        return _norm(tuple(r.get(n) for n in names))

    def minus(rows: list[dict], other: list[dict]) -> list[dict]:
        left = Counter(map(key, other))
        out = []
        for r in rows:
            if left[key(r)] > 0:
                left[key(r)] -= 1
            else:
                out.append(r)
        return out

    missing, unexpected = minus(want, have), minus(have, want)
    lines = []
    if missing:
        lines += [f"  missing ({len(missing)} expected row(s) not produced):", *_listed(missing)]
    if unexpected:
        lines += [f"  unexpected ({len(unexpected)} row(s) not expected):", *_listed(unexpected)]
    return lines


@overload
def assert_contract(
    node: Node, data: None = None, *, expected: None = None, engine: str = "duckdb"
) -> None: ...


@overload
def assert_contract(
    node: Node, data: Mapping[str, Rows], *, expected: Rows | None = None, engine: str = "duckdb"
) -> pa.Table: ...


def assert_contract(
    node: Node,
    data: Mapping[str, Rows] | None = None,
    *,
    expected: Rows | None = None,
    engine: str = "duckdb",
) -> pa.Table | None:
    """Assert that a node's contract is proved, and that it holds on `data`.

    Every contracted transform the node is built from must have its
    postconditions proved and every precondition on another node's result
    proved from that node's guarantees. A transform with
    `on_unproved="error"` (the default) already raises when the node is
    built; this catches `"warn"` and `"runtime"`, which let an unproved
    contract through.

    With `data`, the node runs on those rows: they must meet the
    preconditions (a violation is a mistake in the test data, and is
    reported with the offending rows), and the output must meet the
    postconditions on `engine`. With `expected`, the output must also be
    those rows, compared as bags (doubles to 12 significant digits), with
    the missing and unexpected rows listed when it is not.

    Args:
        node: A node: a source or node piped into contracted transforms
            (`source(...).pipe(paid)`).
        data: The rows of each table the node reads, by name: its sources,
            and the stored nodes it reads (`Node.write`). Default: none,
            which only checks the proof.
        expected: The rows the node should give on `data`: dicts by column
            name, tuples in column order, or an Arrow table.
        engine: Where to run the node: `"duckdb"` (the default),
            `"polars"`, `"datafusion"` or `"spark"`.

    Returns:
        The node's output on `data`, or None without `data`.

    Raises:
        AssertionError: The contract is not proved, the data violates a
            precondition, or the output violates a postcondition or differs
            from `expected`.
        ValueError: `data` misses a table the node reads, or has one it
            does not read.
        TypeError: `node` is not a node, or `expected` is given without
            `data`.

    Examples:
        ```python
        import sverify as sv
        from ibis import _
        from sverify.testing import assert_contract, source

        @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.doubled >= 0])
        def doubled(orders):
            return orders.select(orders.id, doubled=orders.amount * 2)

        orders = source([], {"id": "int64", "amount": "int64"}, name="orders")
        assert_contract(orders.pipe(doubled))
        assert_contract(
            orders.pipe(doubled),
            data={"orders": [(1, 30), (2, 0)]},
            expected=[(1, 60), (2, 0)],
        )
        ```
    """
    __tracebackhide__ = True
    node = _node(node)
    problems = []
    seen: set[int] = set()

    def walk(n: Node) -> None:
        if id(n) in seen:
            return
        seen.add(id(n))
        for i in n._inputs:
            walk(i)
        prov = _lookup(n._expr.op()) if isinstance(n, _Derived) else None
        if prov is None:
            return
        if not prov.report.proved:
            report = "\n".join(f"    {line}" for line in str(prov.report).splitlines())
            problems.append(f"  {n.name}:\n{report}")
        problems.extend(f"  not proved: {link}" for link in prov.unproved_links)

    walk(node)
    if problems:
        raise AssertionError(f"the contract of {node.name} is not proved:\n" + "\n".join(problems))
    if data is None:
        if expected is not None:
            raise TypeError("assert_contract(expected=...) needs data=")
        return None
    out, problems = _output(_connection(node, data), node, engine)
    if problems:
        raise AssertionError(
            f"the output of {node.name} on {engine} violates its proved postconditions "
            "(please report this as a sverify bug):\n" + "\n".join(problems)
        )
    if expected is not None and (diff := _diff(out, expected)):
        raise AssertionError(
            f"{node.name} on {engine} does not give the expected rows:\n" + "\n".join(diff)
        )
    return out


def assert_engines_agree(
    node: Node, data: Mapping[str, Rows], *, engines: Sequence[str] | None = None
) -> pa.Table:
    """Assert that every engine gives the same rows for a node on `data`.

    The rows are compared as bags (doubles to 12 significant digits). The
    data must meet the node's preconditions: outside them the engines may
    rightly disagree. Each output is also checked against the node's
    postconditions.

    Args:
        node: A node: a source or node piped into contracted transforms.
        data: The rows of each table the node reads, by name (see
            `assert_contract`).
        engines: The engines to compare. Default: `installed_engines()`.

    Returns:
        The first engine's output.

    Raises:
        AssertionError: The data violates a precondition, an engine fails or
            violates a postcondition, or two engines give different rows
            (the message lists the rows that differ from the first engine's).
        ValueError: Fewer than two engines, or `data` does not match the
            tables the node reads.

    Examples:
        With `doubled` and `orders` from `assert_contract`'s example:

        ```python
        from sverify.testing import assert_engines_agree

        assert_engines_agree(orders.pipe(doubled), {"orders": [(1, 30), (2, 7)]})
        ```
    """
    __tracebackhide__ = True
    node = _node(node)
    engines = list(engines if engines is not None else installed_engines())
    if len(engines) < 2:
        raise ValueError(f"comparing engines needs at least two, got {engines}")
    con = _connection(node, data)
    outputs: dict[str, pa.Table] = {}
    problems = []
    for engine in engines:
        try:
            outputs[engine], violated = _output(con, node, engine)
        except Exception as e:  # noqa: BLE001 - reported with the other engines' results
            problems.append(f"  {engine} failed: {type(e).__name__}: {e}")
            continue
        if violated:
            problems += [f"  {engine} violates a proved postcondition:", *violated]
    if outputs:
        first, *others = outputs
        for engine in others:
            if diff := _diff(outputs[engine], outputs[first]):
                problems += [f"  {engine} differs from {first}:", *diff]
    if problems:
        raise AssertionError(
            f"the engines disagree on {node.name} ({', '.join(engines)}):\n" + "\n".join(problems)
        )
    return outputs[engines[0]]


def _values(dtype: Any, dom: list[object]) -> Any:
    from hypothesis import strategies as st

    simple = st.sampled_from(dom)
    if dtype.is_integer():
        lo, hi = dtype.bounds
        return st.one_of(simple, st.integers(max(lo, -1000), min(hi, 1000)))
    if dtype.is_string():
        return st.one_of(simple, st.text("abcxyz", max_size=4))
    return simple


def cases(node: Node, *, max_rows: int = 5) -> SearchStrategy[dict[str, pa.Table]]:
    """A Hypothesis strategy of input tables that meet a node's preconditions.

    Each example maps the name of each table the node reads (as in
    `assert_contract`'s `data`) to an Arrow table of at most `max_rows` rows.
    Values are drawn from small ranges, the boundaries of the constants in
    the node's plans (`sverify.counterexample`) and NULL for nullable
    columns; then the rows that violate a precondition (evaluated by Lean,
    `Rel.eval`) are dropped, repeated keys keep their first row, and a
    foreign key that matches nothing takes a value of the referenced column
    (or its row goes). So every example meets the
    preconditions, and the node's guarantees hold on its output.

    Needs Hypothesis (`pip install 'sverify[testing]'`). Integers, doubles,
    strings, booleans, dates and timestamps without a time zone are
    supported.

    Args:
        node: A node: a source or node piped into contracted transforms.
        max_rows: The most rows per table. Default: 5.

    Returns:
        A strategy of `{table name: pyarrow.Table}`.

    Raises:
        TypeError: A column has a type `cases` cannot generate.
        ImportError: Hypothesis is not installed.

    Examples:
        With `doubled` and `orders` from `assert_contract`'s example:

        ```python
        from hypothesis import given, settings
        from sverify.testing import cases

        node = orders.pipe(doubled)

        @settings(max_examples=10, deadline=None)
        @given(cases(node))
        def test_doubled(data):
            out = assert_contract(node, data=data)
            assert out.num_rows == data["orders"].num_rows

        test_doubled()
        ```
    """
    try:
        from hypothesis import strategies as st
    except ImportError as e:
        raise ImportError("cases() needs Hypothesis: pip install 'sverify[testing]'") from e
    node = _node(node)
    leaves = node._leaves()
    schemas = {leaf.name: plain_schema(leaf.schema.to_pyarrow()) for leaf in leaves}
    requirements = _requirements(node, leaves)
    con = connect()
    for name, schema in schemas.items():
        con.put(name, schema.empty_table())
    row_plans = {
        t: [
            json.loads(plan_json(con, condition_query(con.table(t), c)))
            for c in cs
            if not isinstance(c, TableCondition)
        ]
        for t, cs in requirements.items()
    }
    keys = {
        t: [[schemas[t].names.index(col) for col in c.cols] for c in cs if isinstance(c, Unique)]
        for t, cs in requirements.items()
    }
    foreign = [
        (t, schemas[t].names.index(c.col), c.table, schemas[c.table].names.index(c.other))
        for t, cs in requirements.items()
        for c in cs
        if isinstance(c, References)
    ]
    literals = counterexample._plan_literals(
        [json.loads(node.plan), *(p for ps in row_plans.values() for p in ps)]
    )
    tables = {}
    for name, leaf in zip(schemas, leaves, strict=True):
        cols = []
        for col, dtype in leaf.schema.items():
            dom = counterexample.domain(dtype, literals)
            if dom is None:
                raise TypeError(f"cases() cannot generate values of {name}.{col} ({dtype})")
            cols.append(_values(dtype, dom))
        tables[name] = st.lists(st.tuples(*cols), max_size=max_rows)

    def repair(t: str, rows: list[tuple]) -> list[tuple]:
        """`rows` without those that break a row condition or repeat a key."""
        for plan in row_plans[t]:
            if rows:
                held = counterexample.evaluate(plan, {t: rows})
                rows = [r for r, (v,) in zip(rows, held, strict=True) if v is True]
        for cols in keys[t]:
            seen: set[object] = set()
            kept = []
            for r in rows:
                k = _norm(tuple(r[i] for i in cols))
                if k not in seen:
                    seen.add(k)
                    kept.append(r)
            rows = kept
        return rows

    @st.composite
    def admissible(draw: st.DrawFn) -> dict[str, pa.Table]:
        drawn = {t: repair(t, draw(rows)) for t, rows in tables.items()}
        # A foreign key that matches nothing takes a value of the referenced
        # column (then the row is repaired again); what still matches nothing
        # is dropped.
        for t, col, other, other_col in foreign:
            present = [r[other_col] for r in drawn[other]]
            known = {_norm(v) for v in present}
            fixed = [
                r
                if r[col] is None or _norm(r[col]) in known or not present
                else (*r[:col], draw(st.sampled_from(present)), *r[col + 1 :])
                for r in drawn[t]
            ]
            drawn[t] = repair(t, fixed)
        changed = True
        while changed:
            changed = False
            for t, col, other, other_col in foreign:
                known = {_norm(r[other_col]) for r in drawn[other]}
                kept = [r for r in drawn[t] if r[col] is None or _norm(r[col]) in known]
                changed |= len(kept) < len(drawn[t])
                drawn[t] = kept
        return {
            t: pa.Table.from_pylist(
                [dict(zip(schemas[t].names, r, strict=True)) for r in rows], schema=schemas[t]
            )
            for t, rows in drawn.items()
        }

    return admissible()
