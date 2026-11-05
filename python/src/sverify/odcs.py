"""Contracts in the Open Data Contract Standard (ODCS, #791).

ODCS (Bitol, Linux Foundation AI & Data) describes a dataset's contract in
YAML: its schema, quality rules, descriptions and owners. Sverify writes
each node's contract as ODCS and reads ODCS contracts back as conditions.

    from sverify import odcs

    doc = odcs.export(paid_node)              # a dict, ODCS v3.2.0
    odcs.write(paid_node, "paid.odcs.yaml")   # YAML (sverify[odcs]) or JSON

    orders = odcs.read("orders.odcs.yaml")
    @sv.transform(requires={"orders": orders.conditions()})
    def paid(orders): ...

* `export` maps the node's proved contract to ODCS: NOT NULL columns to
  `required`, keys to `primaryKey` and `unique` (or a `duplicateValues`
  rule over several columns), value sets to `invalidValues` rules, row caps
  to `rowCount`, and every other row condition to a `sql` rule. Each rule
  and flag carries a custom property `sverify` (vendor `sverify`) whose
  `status` says how sverify knows it: `proved` by Lean, `checked` on the
  data at every refresh (`on_unproved="check"`), or `declared` and neither.
  Descriptions stay text.
* `read` gives an `OdcsContract`: the conditions sverify reads, per schema
  object, for `requires` on an input or `ensures` on a node, and in
  `unread` every rule it cannot read, with the reason. Unread rules are
  never dropped silently: `read` warns (`UnreadRuleWarning`) and, with
  `strict=True`, raises.

`ODCS_VERSION` is the ODCS release sverify writes (`apiVersion`) and is
tested against; `read` accepts the 3.x releases.
"""

from __future__ import annotations

import hashlib
import json
import re
import uuid
import warnings
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

import sqlglot as sg

if TYPE_CHECKING:
    import ibis

    from sverify.contracts import Condition
    from sverify.nodes import Node

__all__ = [
    "ODCS_VERSION",
    "OdcsContract",
    "Unread",
    "UnreadRuleWarning",
    "export",
    "read",
    "write",
]

#: The ODCS release `export` writes (`apiVersion`), whose JSON schema the
#: tests validate against.
ODCS_VERSION = "v3.2.0"

_READS = ("v3.0.0", "v3.0.1", "v3.0.2", "v3.1.0", "v3.2.0")
_VENDOR = "sverify"
_DIALECT = "duckdb"
_ZERO = ({"mustBe": 0}, {"mustBeLessThan": 1}, {"mustBeLessOrEqualTo": 0})


class UnreadRuleWarning(UserWarning):
    """`read` met rules it cannot read as conditions; `OdcsContract.unread`
    lists them with the reason."""


# -- export ---------------------------------------------------------------------


def _logical(t: Any) -> str:
    if t.is_integer():
        return "integer"
    if t.is_floating() or t.is_decimal():
        return "number"
    if t.is_boolean():
        return "boolean"
    if t.is_timestamp():
        return "timestamp"
    if t.is_date():
        return "date"
    if t.is_time():
        return "time"
    if t.is_array():
        return "array"
    if t.is_map():
        return "map"
    if t.is_struct():
        return "object"
    return "string"


def _physical(t: Any) -> str:
    from ibis.backends.sql.datatypes import DuckDBType

    return DuckDBType.to_string(t)


def _sverify(value: Mapping[str, Any]) -> list[dict[str, Any]]:
    return [{"property": "sverify", "vendor": _VENDOR, "value": dict(value)}]


def _rule_id(label: str) -> str:
    return "sverify_" + hashlib.sha256(label.encode()).hexdigest()[:12]


def _status(c: Any) -> str:
    return "proved" if c.proved else "checked" if c.checked else "declared"


def _quote(col: str) -> str:
    return sg.exp.to_identifier(col, quoted=True).sql(_DIALECT)


def _value_set(sql: str) -> tuple[str, list[Any]] | None:
    """`col IN (literals)` as its column and values."""
    e = sg.parse_one(sql, read="postgres")
    if isinstance(e, sg.exp.Paren):
        e = e.this
    if not isinstance(e, sg.exp.In) or not isinstance(e.this, sg.exp.Column):
        return None
    if e.args.get("query") or not e.expressions:
        return None
    values: list[Any] = []
    for v in e.expressions:
        if isinstance(v, sg.exp.Neg) and isinstance(v.this, sg.exp.Literal):
            v = sg.exp.Literal.number(f"-{v.this.this}")
        if not isinstance(v, sg.exp.Literal):
            return None
        values.append(v.this if v.is_string else _number(v.this))
    return e.this.name, values


def _number(text: str) -> int | float:
    try:
        return int(text)
    except ValueError:
        return float(text)


def _columns(sql: str) -> set[str]:
    return {c.name for c in sg.parse_one(sql, read="postgres").find_all(sg.exp.Column)}


def _sql_rule(sql: str) -> str:
    """The ODCS query counting the rows where `sql` is not TRUE: sverify's
    conditions hold where they are TRUE, so a NULL counts against them."""
    duck = sg.parse_one(sql, read="postgres").sql(_DIALECT)
    return f"SELECT COUNT(*) FROM {{object}} WHERE NOT COALESCE({duck}, FALSE)"


def export(
    node: Node,
    *,
    id: str | None = None,  # noqa: A002 - ODCS's name
    version: str = "1.0.0",
    status: str = "active",
    description: str | None = None,
    descriptions: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    """The contract of `node` as an ODCS document (`ODCS_VERSION`).

    One schema object, named after the node, with a property per column:
    its logical and physical (DuckDB) type, `required` where the node proves
    the column NOT NULL, and `primaryKey` or `unique` for its keys. Value
    sets become `invalidValues` rules, row caps `rowCount` rules, keys over
    several columns `duplicateValues` rules, and other row conditions `sql`
    rules (`SELECT COUNT(*) FROM {object} WHERE NOT COALESCE(<condition>,
    FALSE)`, which must be 0). Every flag and rule carries the custom
    property `sverify` with its `status`: `proved`, `checked` (on the data,
    `on_unproved="check"`) or `declared`. The document's own `sverify`
    property names the node, the plan's sha256 (as the sink's contract
    record has it) and whether the whole contract is proved.

    Args:
        node: A node with a contract (a transform's result, stored or not).
        id: The contract's `id`. Default: a UUID derived from the node's name,
            the same on every export.
        version: The contract's `version`. Default "1.0.0".
        status: The contract's `status`. Default "active".
        description: The dataset's purpose (`description.purpose` and the
            schema object's `description`). Default: the first paragraph of
            the transform's docstring, if any.
        descriptions: A description per column, by name.

    Returns:
        The document as a dict, ready for `json.dump` or `yaml.safe_dump`.

    Raises:
        ValueError: `node` has no contract (a source, or a transform without
            one).
    """
    from sverify.contracts import (
        MaxRows,
        References,
        RowsPer,
        Unique,
        _lookup,
        label,
    )
    from sverify.incremental import plan_digest
    from sverify.io._common import condition_sql, not_null_column
    from sverify.report_json import _sverify_version

    report = node.report
    if report is None:
        raise ValueError(f"{node.name} has no contract to export: it is a source, or no transform")
    schema = node.schema
    prov = _lookup(node._query()._expr.op())
    fn = getattr(getattr(prov, "transform", None), "fn", None)
    if description is None and fn is not None and fn.__doc__:
        description = fn.__doc__.strip().split("\n\n")[0].replace("\n", " ").strip() or None
    descriptions = dict(descriptions or {})

    flags: dict[str, dict[str, str]] = {c: {} for c, _t in schema.items()}
    rules: dict[str | None, list[dict[str, Any]]] = {c: [] for c, _t in schema.items()}
    rules[None] = []
    relationships: dict[str, list[dict[str, Any]]] = {}
    uniques: list[tuple[tuple[str, ...], str]] = []
    rank = {"proved": 2, "checked": 1, "declared": 0}

    def flag(col: str, name: str, st: str) -> None:
        if col in flags and rank[st] > rank.get(flags[col].get(name, ""), -1):
            flags[col][name] = st

    for col in report.not_null:
        flag(col, "required", "proved")
    for c in report.ensures:
        cond, st, lab = c.condition, _status(c), c.label
        if cond is None:
            continue
        meta = _sverify({"status": st, "label": lab})
        rule_id = _rule_id(lab)
        if isinstance(cond, Unique):
            uniques.append((tuple(cond.cols), st))
            continue
        if isinstance(cond, MaxRows):
            rules[None].append(
                {
                    "id": rule_id,
                    "name": lab,
                    "metric": "rowCount",
                    "mustBeLessOrEqualTo": cond.n,
                    "customProperties": meta,
                }
            )
            continue
        if isinstance(cond, RowsPer):
            cols = ", ".join(_quote(x) for x in cond.cols)
            rules[None].append(
                {
                    "id": rule_id,
                    "name": lab,
                    "type": "sql",
                    "query": f"SELECT COUNT(*) FROM (SELECT {cols} FROM {{object}} "
                    f"GROUP BY {cols} HAVING COUNT(*) > {cond.n})",
                    "mustBe": 0,
                    "dimension": "uniqueness",
                    "customProperties": meta,
                }
            )
            continue
        if isinstance(cond, References):
            relationships.setdefault(cond.col, []).append(
                {"type": "foreignKey", "to": f"{cond.table}.{cond.other}"}
            )
            flag(cond.col, "relationship", st)
            continue
        try:
            sql = condition_sql(cond, schema)
        except Exception:  # noqa: BLE001 - not a row condition sverify can write as SQL
            sql = None
        if sql is None:
            rules[None].append(
                {
                    "id": rule_id,
                    "name": lab,
                    "type": "text",
                    "description": lab,
                    "customProperties": meta,
                }
            )
            continue
        if (col := not_null_column(sql)) is not None:
            flag(col, "required", st)
            continue
        if (vs := _value_set(sql)) is not None and vs[0] in rules:
            # TRUE only where the column is not NULL.
            flag(vs[0], "required", st)
            rules[vs[0]].append(
                {
                    "id": rule_id,
                    "name": lab,
                    "metric": "invalidValues",
                    "arguments": {"validValues": vs[1]},
                    "mustBe": 0,
                    "dimension": "conformity",
                    "customProperties": meta,
                }
            )
            continue
        cols = _columns(sql)
        where = next(iter(cols)) if len(cols) == 1 and next(iter(cols)) in rules else None
        rules[where].append(
            {
                "id": rule_id,
                "name": lab,
                "type": "sql",
                "query": _sql_rule(sql),
                "mustBe": 0,
                "dimension": "conformity",
                "customProperties": meta,
            }
        )

    # The first key whose columns are all NOT NULL is the primary key.
    primary: tuple[str, ...] | None = None
    for cols, st in uniques:
        if primary is None and all(flags.get(c, {}).get("required") for c in cols):
            primary = cols
            for c in cols:
                flag(c, "primaryKey", st)
            if len(cols) > 1:
                continue
        if len(cols) == 1:
            flag(cols[0], "unique", st)
        elif cols != primary:
            lab = label(Unique(cols))
            rules[None].append(
                {
                    "id": _rule_id(lab),
                    "name": lab,
                    "metric": "duplicateValues",
                    "arguments": {"properties": list(cols)},
                    "mustBe": 0,
                    "dimension": "uniqueness",
                    "customProperties": _sverify({"status": st, "label": lab}),
                }
            )

    properties = []
    for col, t in schema.items():
        p: dict[str, Any] = {
            "name": col,
            "logicalType": _logical(t),
            "physicalType": _physical(t),
        }
        if col in descriptions:
            p["description"] = descriptions[col]
        f = flags[col]
        if "required" in f:
            p["required"] = True
        if "unique" in f:
            p["unique"] = True
        if "primaryKey" in f and primary is not None:
            p["primaryKey"] = True
            p["primaryKeyPosition"] = primary.index(col) + 1
        if col in relationships:
            p["relationships"] = relationships[col]
        if rules[col]:
            p["quality"] = rules[col]
        if f:
            p["customProperties"] = _sverify({k: v for k, v in f.items()})
        properties.append(p)

    obj: dict[str, Any] = {
        "name": node.name,
        "logicalType": "object",
        "physicalType": "table",
        "properties": properties,
    }
    if (location := getattr(getattr(node, "sink", None), "location", None)) is not None:
        obj["physicalName"] = str(location)
    if description:
        obj["description"] = description
    if rules[None]:
        obj["quality"] = rules[None]

    doc: dict[str, Any] = {
        "apiVersion": ODCS_VERSION,
        "kind": "DataContract",
        "id": id or str(uuid.uuid5(uuid.NAMESPACE_URL, f"sverify:node:{node.name}")),
        "name": node.name,
        "version": version,
        "status": status,
    }
    if description:
        doc["description"] = {"purpose": description}
    doc["schema"] = [obj]
    doc["customProperties"] = _sverify(
        {
            "node": node.name,
            "plan": plan_digest(node.internal_plan),
            "proved": report.proved,
            "semantics": report.semantics,
            "sverify": _sverify_version(),
        }
    )
    return doc


def write(node: Node, path: str | Path, **kwargs: Any) -> dict[str, Any]:
    """Write `export(node, **kwargs)` to `path`: JSON for a `.json` file,
    YAML otherwise (which needs PyYAML: `pip install sverify[odcs]`).

    Args:
        node: The node, as for `export`.
        path: The file to write.
        **kwargs: `export`'s keyword arguments.

    Returns:
        The document written.
    """
    doc = export(node, **kwargs)
    Path(path).write_text(dumps(doc, "json" if str(path).endswith(".json") else "yaml"))
    return doc


def dumps(doc: Mapping[str, Any], fmt: str = "yaml") -> str:
    """`doc` as YAML or JSON text."""
    if fmt == "json":
        return json.dumps(doc, indent=2) + "\n"
    try:
        import yaml
    except ImportError as e:  # pragma: no cover - the extra installs it
        raise ImportError(
            "writing ODCS as YAML needs PyYAML: pip install 'sverify[odcs]', or write JSON"
        ) from e
    return yaml.safe_dump(dict(doc), sort_keys=False, allow_unicode=True)


# -- import ---------------------------------------------------------------------


@dataclass(frozen=True)
class Unread:
    """A rule of an ODCS contract that `read` could not read as a condition.

    Attributes:
        table: The schema object it is on.
        column: The property it is on, or None for a rule on the object.
        rule: The rule (or the property's field) as the document has it.
        reason: Why sverify cannot read it.
    """

    table: str
    column: str | None
    rule: Any
    reason: str

    def __str__(self) -> str:
        where = self.table if self.column is None else f"{self.table}.{self.column}"
        return f"{where}: {self.reason}: {json.dumps(self.rule, default=str)}"


@dataclass
class OdcsContract:
    """An ODCS contract as `read` gives it.

    Attributes:
        document: The document as read.
        tables: The conditions sverify reads, per schema object, in the
            document's order.
        unread: The rules sverify cannot read, with the reason.
    """

    document: dict[str, Any]
    tables: dict[str, list[Condition]] = field(default_factory=dict)
    unread: list[Unread] = field(default_factory=list)

    def _table(self, table: str | None) -> str:
        if table is None:
            if len(self.tables) != 1:
                raise ValueError(
                    f"the contract has {len(self.tables)} schema objects "
                    f"({', '.join(self.tables) or 'none'}): name one"
                )
            return next(iter(self.tables))
        if table not in self.tables:
            raise KeyError(f"the contract has no schema object {table!r}")
        return table

    def conditions(self, table: str | None = None) -> list[Condition]:
        """The conditions on schema object `table` (the only one by default),
        for `requires={"orders": ...}` or `ensures=...`.

        Args:
            table: The schema object's name. Default: the contract's only one.

        Returns:
            The conditions: SQL strings, `sv.unique`, `sv.key`,
            `sv.max_rows`, `sv.rows_per` and `sv.references`.
        """
        return list(self.tables[self._table(table)])

    def schema(self, table: str | None = None) -> ibis.Schema:
        """The columns of schema object `table` and their types: the
        physical type where DuckDB reads it, else the logical type.

        Args:
            table: The schema object's name. Default: the contract's only one.

        Returns:
            An Ibis schema.
        """
        import ibis

        name = self._table(table)
        obj = next(o for o in self.document.get("schema") or [] if o.get("name") == name)
        cols = {}
        for p in obj.get("properties") or []:
            cols[p["name"]] = _ibis_type(p)
        return ibis.schema(cols)


_LOGICAL_IBIS = {
    "string": "string",
    "integer": "int64",
    "number": "float64",
    "boolean": "boolean",
    "date": "date",
    "timestamp": "timestamp",
    "time": "time",
}


def _ibis_type(p: Mapping[str, Any]) -> Any:
    import ibis.expr.datatypes as dt
    from ibis.backends.sql.datatypes import DuckDBType

    nullable = not p.get("required", False)
    if (phys := p.get("physicalType")) is not None:
        try:
            return DuckDBType.from_string(str(phys), nullable=nullable)
        except Exception:  # noqa: BLE001, S110 - another database's type: use the logical one
            pass
    logical = _LOGICAL_IBIS.get(p.get("logicalType", "string"), "string")
    return dt.dtype(logical).copy(nullable=nullable)


def _load(source: str | Path | Mapping[str, Any]) -> dict[str, Any]:
    if isinstance(source, Mapping):
        return dict(source)
    text = str(source)
    path = Path(text) if "\n" not in text and len(text) < 4096 else None
    if path is not None and path.is_file():
        text = path.read_text()
        if path.suffix == ".json":
            return json.loads(text)
    stripped = text.lstrip()
    if stripped.startswith("{"):
        return json.loads(text)
    try:
        import yaml
    except ImportError as e:  # pragma: no cover - the extra installs it
        raise ImportError("reading ODCS YAML needs PyYAML: pip install 'sverify[odcs]'") from e
    return yaml.safe_load(text)


def _ident(col: str) -> sg.exp.Expr:
    return sg.exp.column(col, quoted=True)


def _lit(v: Any) -> sg.exp.Expr:
    if isinstance(v, bool):
        return sg.exp.Boolean(this=v)
    if isinstance(v, int | float):
        return sg.exp.Literal.number(v)
    return sg.exp.Literal.string(str(v))


def _or_null(col: str, e: sg.exp.Expr, required: bool) -> str:
    """`e`, or NULL in `col` too where the column may be NULL: ODCS's rules
    on values leave NULLs to `required`."""
    if required:
        return e.sql(_DIALECT)
    return sg.exp.or_(sg.exp.paren(e), _ident(col).is_(sg.exp.null())).sql(_DIALECT)


def _is_zero(rule: Mapping[str, Any]) -> bool:
    return any(all(rule.get(k) == v for k, v in z.items()) for z in _ZERO)


_COUNT_WHERE = re.compile(
    r"^\s*SELECT\s+COUNT\s*\(\s*\*\s*\)\s+FROM\s+\{object\}\s+WHERE\s+(?P<where>.+?)\s*;?\s*$",
    re.IGNORECASE | re.DOTALL,
)


def _not_coalesce(e: sg.exp.Expr) -> sg.exp.Expr | None:
    """X of `NOT COALESCE(X, FALSE)`."""
    if isinstance(e, sg.exp.Paren):
        e = e.this
    if not isinstance(e, sg.exp.Not):
        return None
    inner = e.this
    if isinstance(inner, sg.exp.Paren):
        inner = inner.this
    if (
        isinstance(inner, sg.exp.Coalesce)
        and len(inner.expressions) == 1
        and isinstance(inner.expressions[0], sg.exp.Boolean)
        and not inner.expressions[0].this
    ):
        return inner.this
    return None


def _rows_per(query: str, cols: set[str]) -> Any | None:
    """`rows_per` of `SELECT COUNT(*) FROM (SELECT k FROM {object} GROUP BY k
    HAVING COUNT(*) > n)`."""
    from sverify.contracts import rows_per

    try:
        e = sg.parse_one(query.replace("{object}", "__object__"), read=_DIALECT)
    except sg.errors.ParseError:
        return None
    sub = e.args.get("from_") or e.args.get("from")
    inner = getattr(sub, "this", None)
    if isinstance(inner, sg.exp.Subquery):
        inner = inner.this
    if not isinstance(inner, sg.exp.Select):
        return None
    group, having = inner.args.get("group"), inner.args.get("having")
    if group is None or having is None:
        return None
    keys = [k.name for k in group.expressions if isinstance(k, sg.exp.Column)]
    cond = having.this
    if (
        len(keys) != len(group.expressions)
        or not keys
        or not set(keys) <= cols
        or not isinstance(cond, sg.exp.GT)
        or not isinstance(cond.this, sg.exp.Count)
        or not isinstance(cond.expression, sg.exp.Literal)
    ):
        return None
    return rows_per(keys, int(cond.expression.this))


class _Reader:
    def __init__(self, table: str, cols: Mapping[str, Mapping[str, Any]]):
        self.table = table
        self.cols = cols
        self.out: list[Any] = []
        self.unread: list[Unread] = []
        self.valued: set[str] = set()
        """Required columns an IN list covers: TRUE only on a value, it
        implies NOT NULL, which the checker does not always derive."""

    def skip(self, column: str | None, rule: Any, reason: str) -> None:
        self.unread.append(Unread(self.table, column, rule, reason))

    def required(self, col: str | None) -> bool:
        return col is not None and bool(self.cols.get(col, {}).get("required"))

    def sql(self, column: str | None, rule: Mapping[str, Any]) -> None:
        query = str(rule.get("query", ""))
        if column is not None:
            query = query.replace("{property}", _quote(column))
        if not _is_zero(rule):
            self.skip(column, rule, "a threshold on a count: sverify reads rules that must be 0")
            return
        if (rp := _rows_per(query, set(self.cols))) is not None:
            self.out.append(rp)
            return
        m = _COUNT_WHERE.match(query)
        if m is None:
            self.skip(
                column,
                rule,
                "a SQL rule of another shape: sverify reads "
                "SELECT COUNT(*) FROM {object} WHERE <rows that break it>",
            )
            return
        try:
            where = sg.parse_one(m["where"], read=_DIALECT)
        except sg.errors.ParseError as e:
            self.skip(column, rule, f"SQL that does not parse: {e}")
            return
        unknown = {c.name for c in where.find_all(sg.exp.Column)} - set(self.cols)
        if unknown or where.find(sg.exp.Select):
            self.skip(column, rule, f"reads columns the object lacks: {sorted(unknown)}")
            return
        if (x := _not_coalesce(where)) is not None:
            self.out.append(x.sql(_DIALECT))
        else:
            self.out.append(
                sg.exp.not_(
                    sg.exp.Coalesce(this=sg.exp.paren(where), expressions=[sg.exp.false()])
                ).sql(_DIALECT)
            )

    def library(self, column: str | None, rule: Mapping[str, Any]) -> None:
        from sverify.contracts import max_rows, unique

        metric = rule.get("metric") or rule.get("rule")
        args = rule.get("arguments") or {}
        if rule.get("unit") == "percent":
            self.skip(column, rule, "a share of rows: sverify reads rules on every row")
            return
        if metric == "rowCount":
            n = None
            if "mustBeLessOrEqualTo" in rule:
                n = rule["mustBeLessOrEqualTo"]
            elif "mustBeLessThan" in rule:
                n = rule["mustBeLessThan"] - 1
            elif "mustBeBetween" in rule and min(rule["mustBeBetween"]) <= 0:
                n = max(rule["mustBeBetween"])
            if n is None or n != int(n) or n < 0:
                self.skip(column, rule, "a lower bound on the row count: sverify reads caps")
            else:
                self.out.append(max_rows(int(n)))
            return
        if not _is_zero(rule):
            self.skip(column, rule, "a threshold on a count: sverify reads rules that must be 0")
            return
        if metric == "duplicateValues":
            cols = args.get("properties") or ([column] if column else [])
            if not cols or not set(cols) <= set(self.cols):
                self.skip(column, rule, "a key over columns the object lacks")
            else:
                self.out.append(unique(*cols))
            return
        if column is None:
            self.skip(column, rule, f"metric {metric!r} on a whole object")
            return
        if metric == "nullValues":
            self.out.append(_ident(column).is_(sg.exp.null()).not_().sql(_DIALECT))
        elif metric == "missingValues":
            values = [v for v in args.get("missingValues") or [] if v is not None]
            e = sg.exp.not_(_ident(column).is_(sg.exp.null()))
            if values:
                e = sg.exp.and_(
                    e, sg.exp.not_(sg.exp.In(this=_ident(column), expressions=map(_lit, values)))
                )
            self.out.append(e.sql(_DIALECT))
        elif metric == "invalidValues" and "validValues" in args and "pattern" not in args:
            values = list(args["validValues"])
            e = sg.exp.In(this=_ident(column), expressions=[_lit(v) for v in values])
            self.out.append(_or_null(column, e, self.required(column)))
            if self.required(column):
                self.valued.add(column)
        elif metric == "invalidValues":
            self.skip(
                column,
                rule,
                "a pattern: ODCS's regular expressions are ECMA-262, the engines' differ",
            )
        else:
            self.skip(column, rule, f"metric {metric!r} sverify does not read")

    def rule(self, column: str | None, rule: Any) -> None:
        if not isinstance(rule, Mapping):
            self.skip(column, rule, "not a rule")
            return
        kind = rule.get("type") or ("library" if rule.get("metric") or rule.get("rule") else None)
        if kind == "library":
            self.library(column, rule)
        elif kind == "sql":
            self.sql(column, rule)
        elif kind == "text":
            self.skip(column, rule, "free text")
        elif kind == "custom":
            self.skip(column, rule, f"a rule for engine {rule.get('engine')!r}")
        else:
            self.skip(column, rule, f"a rule of type {kind!r}")

    def property(self, p: Mapping[str, Any]) -> None:
        from sverify.contracts import references, unique

        col = p["name"]
        start = len(self.out)
        if p.get("unique") and not p.get("primaryKey"):
            self.out.append(unique(col))
        if enum := p.get("enum"):
            values = [v.get("value") if isinstance(v, Mapping) else v for v in enum]
            e = sg.exp.In(this=_ident(col), expressions=[_lit(v) for v in values])
            self.out.append(_or_null(col, e, self.required(col)))
            if self.required(col):
                self.valued.add(col)
        opts = p.get("logicalTypeOptions") or {}
        logical = p.get("logicalType")
        cast = {"date": "DATE", "timestamp": "TIMESTAMP", "time": "TIME"}.get(str(logical))
        bounds = [
            ("minimum", sg.exp.GTE),
            ("exclusiveMinimum", sg.exp.GT),
            ("maximum", sg.exp.LTE),
            ("exclusiveMaximum", sg.exp.LT),
        ]
        for key, op in bounds:
            if key not in opts:
                continue
            v = opts[key]
            lit = _lit(v)
            if cast is not None:
                lit = sg.exp.cast(sg.exp.Literal.string(str(v)), cast)
            elif not isinstance(v, int | float) or isinstance(v, bool):
                self.skip(col, {key: v}, f"a {key} sverify cannot read for {logical}")
                continue
            self.out.append(_or_null(col, op(this=_ident(col), expression=lit), self.required(col)))
        for key, op in (("minLength", sg.exp.GTE), ("maxLength", sg.exp.LTE)):
            if key in opts:
                e = op(this=sg.exp.Length(this=_ident(col)), expression=_lit(int(opts[key])))
                self.out.append(_or_null(col, e, self.required(col)))
        for key in ("pattern", "format", "multipleOf"):
            if key in opts:
                self.skip(col, {key: opts[key]}, f"logicalTypeOptions.{key}")
        for rel in p.get("relationships") or []:
            to = rel.get("to") if isinstance(rel, Mapping) else None
            if (
                isinstance(rel, Mapping)
                and rel.get("type", "foreignKey") == "foreignKey"
                and isinstance(to, str)
                and to.count(".") == 1
            ):
                table, other = to.split(".")
                self.out.append(references(col, to=(table, other)))
            else:
                self.skip(col, rel, "a relationship sverify does not read")
        for r in p.get("quality") or []:
            self.rule(col, r)
        if p.get("required") and col not in self.valued:
            self.out.insert(start, _ident(col).is_(sg.exp.null()).not_().sql(_DIALECT))


def read(
    source: str | Path | Mapping[str, Any],
    *,
    strict: bool = False,
) -> OdcsContract:
    """Read an ODCS contract as conditions.

    Each schema object gives a list of conditions (`OdcsContract.conditions`):
    `required` columns NOT NULL, the `primaryKey` columns `sv.key`,
    `unique` columns and `duplicateValues` rules `sv.unique`, value sets
    (`enum`, `invalidValues` with `validValues`) `IN` lists, the bounds in
    `logicalTypeOptions` comparisons, `rowCount` caps `sv.max_rows`, foreign
    keys `sv.references`, and `sql` rules of the form `SELECT COUNT(*) FROM
    {object} WHERE <rows that break it>` that must be 0 the condition that
    no row is counted. ODCS leaves NULLs to `required`, so on a column that
    may be NULL a rule on values lets NULL through.

    Every other rule (free text, a custom engine's, a pattern, a threshold
    other than 0, a share of rows) is listed in `unread`, with the reason,
    and `read` warns.

    Args:
        source: A file (YAML, or JSON by its `.json` suffix), the document's
            text, or the document as a dict.
        strict: Raise if any rule is unread. Default False: warn.

    Returns:
        An `OdcsContract`.

    Raises:
        ValueError: The document is no ODCS 3.x contract, or with `strict`,
            some rule is unread.
    """
    doc = _load(source)
    if not isinstance(doc, dict) or doc.get("kind", "DataContract") != "DataContract":
        raise ValueError("not an ODCS data contract (kind: DataContract)")
    api = doc.get("apiVersion")
    if api not in _READS:
        raise ValueError(
            f"ODCS apiVersion {api!r}: sverify reads {', '.join(_READS)}; it writes {ODCS_VERSION}"
        )
    from sverify.contracts import key

    out = OdcsContract(doc)
    for obj in doc.get("schema") or []:
        name = obj.get("name")
        props = {p["name"]: p for p in obj.get("properties") or [] if "name" in p}
        r = _Reader(name, props)
        pk = sorted(
            (p for p in props.values() if p.get("primaryKey")),
            key=lambda p: p.get("primaryKeyPosition", -1),
        )
        if pk:
            r.out.append(key(*(p["name"] for p in pk)))
        for p in props.values():
            r.property(p)
        for rel in obj.get("relationships") or []:
            r.skip(None, rel, "a relationship on the object")
        for rule in obj.get("quality") or []:
            r.rule(None, rule)
        out.tables[name] = _dedupe(r.out)
        out.unread += r.unread
    if out.unread:
        text = "\n".join(f"  {u}" for u in out.unread)
        if strict:
            raise ValueError(f"{len(out.unread)} ODCS rule(s) sverify cannot read:\n{text}")
        warnings.warn(
            f"{len(out.unread)} ODCS rule(s) sverify cannot read (OdcsContract.unread):\n{text}",
            UnreadRuleWarning,
            stacklevel=2,
        )
    return out


def _dedupe(conds: Sequence[Any]) -> list[Any]:
    from sverify.contracts import label

    seen: set[str] = set()
    out = []
    for c in conds:
        lab = label(c)
        if lab not in seen:
            seen.add(lab)
            out.append(c)
    return out
