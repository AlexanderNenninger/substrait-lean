"""ODCS (#791): a node's contract exported as an Open Data Contract Standard
document, valid against ODCS v3.2.0's JSON schema (`tests/standards/`), and
ODCS contracts read back as conditions, with the rules sverify cannot read
listed."""

from __future__ import annotations

import json
import textwrap
import warnings
from pathlib import Path

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import odcs
from sverify.cli import main
from sverify.contracts import Key, MaxRows, References, RowsPer, Unique, label
from sverify.io import StaticSource

# The wheel's tests install only what the Wheels workflow lists.
jsonschema = pytest.importorskip("jsonschema")
yaml = pytest.importorskip("yaml")

SCHEMA = json.loads(
    (Path(__file__).parent / "standards" / f"odcs-json-schema-{odcs.ODCS_VERSION}.json").read_text()
)


# Checked once: `jsonschema.validate` checks the 110 KB schema itself on
# every call, 83 ms against 5 ms for a document.
jsonschema.validators.validator_for(SCHEMA).check_schema(SCHEMA)
VALIDATOR = jsonschema.validators.validator_for(SCHEMA)(SCHEMA)


def valid(doc: dict) -> dict:
    VALIDATOR.validate(doc)
    return doc


def orders() -> StaticSource:
    return StaticSource(
        pa.table(
            {
                "id": [1, 2, 3],
                "status": ["paid", "open", "paid"],
                "amount": [30, 5, 50],
                "customer": ["a", "b", "a"],
            }
        ),
        name="orders",
    )


REQUIRES = [
    _.amount >= 0,
    _.amount < 1000,
    sv.key("id"),
    _.id >= 0,
    _.status.isin(["paid", "open"]),
    sv.max_rows(10_000),
]


def paid_node(**kwargs):
    @sv.transform(
        requires={"orders": REQUIRES},
        ensures=[
            _.amount > 10,
            sv.key("id"),
            _.status.isin(["paid", "open"]),
            sv.max_rows(10_000),
            sv.unique("customer", "status", "id"),
            "amount + id > 0",
        ],
        **kwargs,
    )
    def paid(orders):
        """Paid orders over ten.

        Read by the revenue report."""
        return orders.filter(orders.amount > 10)

    return orders().pipe(paid)


def prop(doc: dict, name: str) -> dict:
    return next(p for p in doc["schema"][0]["properties"] if p["name"] == name)


def status(rule_or_prop: dict) -> dict:
    (cp,) = [c for c in rule_or_prop["customProperties"] if c["property"] == "sverify"]
    assert cp["vendor"] == "sverify"
    return cp["value"]


def test_export_validates_and_maps_the_contract():
    doc = valid(odcs.export(paid_node(), descriptions={"id": "the order's id"}))
    assert doc["apiVersion"] == "v3.2.0" and doc["kind"] == "DataContract"
    assert doc["description"] == {"purpose": "Paid orders over ten."}
    (obj,) = doc["schema"]
    assert obj["name"] == "paid" and obj["description"] == "Paid orders over ten."
    id_ = prop(doc, "id")
    assert id_["required"] and id_["primaryKey"] and id_["primaryKeyPosition"] == 1
    assert id_["description"] == "the order's id"
    assert id_["logicalType"] == "integer" and id_["physicalType"] == "BIGINT"
    assert status(id_) == {"required": "proved", "primaryKey": "proved", "unique": "proved"}
    # A value set: an `invalidValues` rule, and NOT NULL, since IN is TRUE
    # only on a value.
    st = prop(doc, "status")
    (rule,) = st["quality"]
    assert rule["metric"] == "invalidValues" and rule["mustBe"] == 0
    assert rule["arguments"] == {"validValues": ["paid", "open"]}
    assert status(rule)["status"] == "proved" and st["required"]
    # A range: a SQL rule on the column.
    (rng,) = prop(doc, "amount")["quality"]
    assert rng["type"] == "sql" and rng["mustBe"] == 0
    assert rng["query"] == "SELECT COUNT(*) FROM {object} WHERE NOT COALESCE(amount > 10, FALSE)"
    # On the object: the row cap, the key over three columns, and the
    # condition over two.
    kinds = {r.get("metric") or r["type"]: r for r in obj["quality"]}
    assert kinds["rowCount"]["mustBeLessOrEqualTo"] == 10_000
    assert kinds["duplicateValues"]["arguments"] == {"properties": ["customer", "status", "id"]}
    assert "amount + id > 0" in kinds["sql"]["query"]
    top = status(doc)
    assert top["node"] == "paid" and top["proved"] is True and len(top["plan"]) == 64


def test_export_marks_checked_and_declared_rules():
    @sv.transform(
        requires={"orders": REQUIRES},
        ensures=[_.amount > 10, _.amount > 20],
        on_unproved="check",
    )
    def checked(orders):
        return orders.filter(orders.amount > 10)

    doc = valid(odcs.export(orders().pipe(checked)))
    rules = {r["name"]: status(r)["status"] for r in prop(doc, "amount")["quality"]}
    assert rules == {"(_.amount > 10)": "proved", "(_.amount > 20)": "checked"}
    assert status(doc)["proved"] is False


def test_export_is_stable():
    a, b = odcs.export(paid_node()), odcs.export(paid_node())
    assert a == b


def test_export_needs_a_contract():
    with pytest.raises(ValueError, match="no contract"):
        odcs.export(sv.nodes._source_node(orders()))


def _rules(doc: dict) -> dict:
    """What a document says, without names, ids and labels."""

    def strip(r: dict) -> dict:
        return {
            k: v
            for k, v in r.items()
            if k not in ("id", "name", "customProperties", "dimension", "description")
        }

    out: dict = {
        "object": sorted(json.dumps(strip(r)) for r in doc["schema"][0].get("quality", []))
    }
    for p in doc["schema"][0]["properties"]:
        out[p["name"]] = {
            "flags": {k: p.get(k) for k in ("required", "unique", "primaryKey")},
            "quality": sorted(json.dumps(strip(r)) for r in p.get("quality", [])),
        }
    return out


def test_round_trip_keeps_every_rule():
    first = odcs.export(paid_node())
    contract = odcs.read(first, strict=True)
    assert contract.unread == []
    conds = contract.conditions("paid")

    @sv.transform(requires={"orders": REQUIRES}, ensures=conds)
    def paid(orders):
        return orders.filter(orders.amount > 10)

    second = valid(odcs.export(orders().pipe(paid)))
    assert _rules(second) == _rules(first)
    assert all(status(r)["status"] == "proved" for r in second["schema"][0]["quality"])


def test_round_trip_through_yaml_and_json(tmp_path):
    node = paid_node()
    for name in ("paid.odcs.yaml", "paid.odcs.json"):
        path = tmp_path / name
        written = odcs.write(node, path)
        text = path.read_text()
        assert (json.loads(text) if name.endswith(".json") else yaml.safe_load(text)) == written
        back = odcs.read(path, strict=True)
        assert [label(c) for c in back.conditions()] == [
            label(c) for c in odcs.read(written).conditions()
        ]


DOC = textwrap.dedent(
    """
    apiVersion: v3.1.0
    kind: DataContract
    id: orders-contract
    version: 2.0.0
    status: active
    schema:
      - name: orders
        properties:
          - name: id
            logicalType: integer
            physicalType: BIGINT
            primaryKey: true
            primaryKeyPosition: 1
          - name: amount
            logicalType: number
            physicalType: DECIMAL(10,2)
            required: true
            logicalTypeOptions: {minimum: 0, exclusiveMaximum: 1000000}
          - name: currency
            logicalType: string
            quality:
              - metric: invalidValues
                arguments: {validValues: [EUR, USD]}
                mustBe: 0
              - metric: invalidValues
                arguments: {pattern: "^[A-Z]{3}$"}
                mustBe: 0
          - name: customer_id
            logicalType: integer
            relationships:
              - to: customers.id
          - name: ordered_at
            logicalType: date
            logicalTypeOptions: {minimum: "2020-01-01"}
          - name: email
            logicalType: string
            unique: true
            quality:
              - metric: nullValues
                mustBe: 0
              - metric: duplicateValues
                mustBeLessThan: 10
        quality:
          - metric: rowCount
            mustBeLessOrEqualTo: 5000000
          - metric: rowCount
            mustBeGreaterThan: 100
          - type: sql
            query: SELECT COUNT(*) FROM {object} WHERE amount > 500 AND currency = 'USD'
            mustBe: 0
          - type: sql
            query: SELECT AVG(amount) FROM {object}
            mustBeLessThan: 300
          - type: sql
            query: |
              SELECT COUNT(*) FROM (SELECT customer_id FROM {object}
              GROUP BY customer_id HAVING COUNT(*) > 50)
            mustBe: 0
          - type: text
            description: Orders arrive within a day.
          - type: custom
            engine: soda
            implementation: "freshness(ordered_at) < 1d"
    """
)


def test_read_maps_rules_to_conditions():
    with pytest.warns(odcs.UnreadRuleWarning, match="6 ODCS rule"):
        c = odcs.read(DOC)
    conds = c.conditions()
    labels = [label(x) for x in conds]
    assert isinstance(conds[0], Key) and conds[0].cols == ("id",)
    assert 'NOT "amount" IS NULL' in labels
    assert '"amount" >= 0' in labels and '"amount" < 1000000' in labels
    # A rule on values lets NULL through where the column may be NULL.
    assert "(\"currency\" IN ('EUR', 'USD')) OR \"currency\" IS NULL" in labels
    assert '("ordered_at" >= CAST(\'2020-01-01\' AS DATE)) OR "ordered_at" IS NULL' in labels
    assert 'NOT "email" IS NULL' in labels
    assert any(isinstance(x, Unique) and x.cols == ("email",) for x in conds)
    assert any(
        isinstance(x, References)
        and (x.col, x.table, x.other) == ("customer_id", "customers", "id")
        for x in conds
    )
    assert any(isinstance(x, MaxRows) and x.n == 5_000_000 for x in conds)
    assert any(isinstance(x, RowsPer) and x.cols == ("customer_id",) and x.n == 50 for x in conds)
    assert "NOT COALESCE((amount > 500 AND currency = 'USD'), FALSE)" in labels
    reasons = sorted(u.reason.split(":")[0] for u in c.unread)
    assert reasons == [
        "a lower bound on the row count",
        "a pattern",
        "a rule for engine 'soda'",
        "a threshold on a count",
        "a threshold on a count",
        "free text",
    ]
    assert str(c.schema()) == str(
        ibis.schema(
            {
                "id": "int64",
                "amount": "!decimal(10, 2)",
                "currency": "string",
                "customer_id": "int64",
                "ordered_at": "date",
                "email": "string",
            }
        )
    )


def test_read_strict_raises_on_unread_rules():
    with pytest.raises(ValueError, match="6 ODCS rule"):
        odcs.read(DOC, strict=True)


def test_read_rejects_other_documents():
    with pytest.raises(ValueError, match="apiVersion"):
        odcs.read({"apiVersion": "v9", "kind": "DataContract", "id": "x", "version": "1"})
    with pytest.raises(ValueError, match="not an ODCS"):
        odcs.read({"kind": "DataProduct"})


def test_read_conditions_are_requires_a_transform_proves_with():
    doc = textwrap.dedent(
        """
        apiVersion: v3.2.0
        kind: DataContract
        id: orders
        version: 1.0.0
        schema:
          - name: orders
            properties:
              - {name: id, logicalType: integer, primaryKey: true}
              - name: amount
                logicalType: integer
                required: true
                logicalTypeOptions: {minimum: 0, maximum: 1000}
        """
    )
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        c = odcs.read(doc)

    @sv.transform(requires={"orders": c.conditions()}, ensures=[_.doubled <= 2000, sv.key("id")])
    def doubled(orders):
        return orders.select(orders.id, doubled=orders.amount * 2)

    assert doubled.check(orders=c.schema()).verdict == sv.Verdict.PROVED


def test_cli_contract_export(tmp_path, capsys):
    path = tmp_path / "pipe.py"
    path.write_text(
        textwrap.dedent(
            """
            import pyarrow as pa
            import sverify as sv
            from ibis import _
            from sverify.io import StaticSource

            orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")

            @sv.transform(
                requires={"orders": [_.amount >= 0, _.amount < 1000, sv.key("id")]},
                ensures=[_.amount > 10, sv.key("id")],
            )
            def paid(orders):
                return orders.filter(orders.amount > 10)

            p = orders.pipe(paid)
            """
        )
    )
    assert main(["contract", "export", f"{path}:p", "--format", "odcs"]) == 0
    doc = valid(yaml.safe_load(capsys.readouterr().out))
    assert prop(doc, "id")["primaryKey"]
    out = tmp_path / "paid.json"
    assert main(["contract", "export", f"{path}:p", "-o", str(out), "--id", "paid-v1"]) == 0
    assert valid(json.loads(out.read_text()))["id"] == "paid-v1"
    assert main(["contract", "export", f"{path}:nope"]) != 0


READ_MORE = {
    "apiVersion": "v3.1.0",
    "kind": "DataContract",
    "id": "more",
    "version": "1",
    "schema": [
        {
            "name": "t",
            "properties": [
                {
                    "name": "code",
                    "logicalType": "string",
                    "required": True,
                    "enum": [{"value": "a"}, "b"],
                    "logicalTypeOptions": {"minLength": 1, "maxLength": 3, "pattern": "^[a-z]+$"},
                },
                {
                    "name": "n",
                    "logicalType": "integer",
                    "logicalTypeOptions": {"exclusiveMinimum": 0, "maximum": 9, "multipleOf": 3},
                    "quality": [
                        {
                            "metric": "missingValues",
                            "arguments": {"missingValues": [None]},
                            "mustBe": 0,
                        },
                        {"metric": "nullValues", "unit": "percent", "mustBeLessThan": 5},
                        {"metric": "averageValue", "mustBe": 0},
                    ],
                },
                {
                    "name": "d",
                    "logicalType": "date",
                    "logicalTypeOptions": {"maximum": "2030-01-01"},
                    "relationships": [{"to": "a.b.c"}, {"type": "other", "to": "x.y"}, "x"],
                },
                {"name": "b", "logicalType": "boolean", "logicalTypeOptions": {"minimum": True}},
            ],
            "relationships": [{"to": "elsewhere.id"}],
            "quality": [
                {"metric": "rowCount", "mustBeLessThan": 11},
                {"metric": "rowCount", "mustBeBetween": [0, 20]},
                {"metric": "rowCount", "mustBeLessOrEqualTo": 2.5},
                {
                    "metric": "duplicateValues",
                    "arguments": {"properties": ["code", "n"]},
                    "mustBe": 0,
                },
                {"metric": "duplicateValues", "arguments": {"properties": ["nope"]}, "mustBe": 0},
                {"metric": "nullValues", "mustBe": 0},
                {
                    "type": "sql",
                    "query": "SELECT COUNT(*) FROM {object} WHERE nope > 1",
                    "mustBe": 0,
                },
                {"type": "sql", "query": "SELECT COUNT(*) FROM {object} WHERE n >", "mustBe": 0},
                {
                    "type": "sql",
                    "query": "SELECT COUNT(*) FROM {object} WHERE n IN (SELECT 1)",
                    "mustBe": 0,
                },
                {"type": "sql", "query": "SELECT 1", "mustBe": 0},
                {"type": "sql", "query": "SELECT COUNT(*) FROM {object} WHERE n > 5", "mustBe": 0},
                {"type": "weird"},
                "not a rule",
            ],
        }
    ],
}


def test_read_lists_what_it_cannot_read_with_reasons():
    with pytest.warns(odcs.UnreadRuleWarning):
        c = odcs.read(READ_MORE)
    labels = [label(x) for x in c.tables["t"]]
    # Bounds and lengths become conditions; required + an IN list needs no
    # separate NOT NULL.
    assert "\"code\" IN ('a', 'b')" in labels
    assert 'NOT "code" IS NULL' not in labels
    assert 'LENGTH("code") >= 1' in labels and 'LENGTH("code") <= 3' in labels
    assert '("n" > 0) OR "n" IS NULL' in labels and '("n" <= 9) OR "n" IS NULL' in labels
    assert '("d" <= CAST(\'2030-01-01\' AS DATE)) OR "d" IS NULL' in labels
    # A row cap from `mustBeLessThan` (n - 1) and from a range starting at 0.
    caps = sorted(x.n for x in c.tables["t"] if isinstance(x, MaxRows))
    assert caps == [10, 20]
    assert any(isinstance(x, Unique) and x.cols == ("code", "n") for x in c.tables["t"])
    assert not any(isinstance(x, References) for x in c.tables["t"])
    assert 'NOT "n" IS NULL' in labels  # missingValues: [null]
    assert "NOT COALESCE((n > 5), FALSE)" in labels
    reasons = [u.reason for u in c.unread]
    expect = [
        "logicalTypeOptions.pattern",
        "logicalTypeOptions.multipleOf",
        "a share of rows",
        "metric 'averageValue' sverify does not read",
        "a relationship sverify does not read",
        "a relationship sverify does not read",
        "a relationship sverify does not read",
        "a minimum sverify cannot read for boolean",
        "a relationship on the object",
        "a lower bound on the row count",
        "a key over columns the object lacks",
        "metric 'nullValues' on a whole object",
        "reads columns the object lacks",
        "SQL that does not parse",
        "reads columns the object lacks",
        "a SQL rule of another shape",
        "a rule of type 'weird'",
        "not a rule",
    ]
    for want in expect:
        assert any(r.startswith(want) for r in reasons), (want, reasons)
    assert len(reasons) == len(expect)


def test_export_maps_every_column_type():
    table = pa.table(
        {
            "i": pa.array([1], pa.int32()),
            "f": pa.array([1.5], pa.float64()),
            "dec": pa.array([1], pa.decimal128(10, 2)),
            "b": pa.array([True]),
            "ts": pa.array([0], pa.timestamp("us")),
            "d": pa.array([0], pa.date32()),
            "t": pa.array([0], pa.time64("us")),
            "arr": pa.array([[1]], pa.list_(pa.int64())),
            "st": pa.array([{"x": 1}], pa.struct([("x", pa.int64())])),
            "s": pa.array(["a"]),
        }
    )

    @sv.transform(requires={"w": []}, ensures=[sv.max_rows(5)], on_unproved="check")
    def passthrough(w):
        return w

    doc = valid(odcs.export(StaticSource(table, name="w").pipe(passthrough)))
    logical = {p["name"]: p["logicalType"] for p in doc["schema"][0]["properties"]}
    assert logical == {
        "i": "integer",
        "f": "number",
        "dec": "number",
        "b": "boolean",
        "ts": "timestamp",
        "d": "date",
        "t": "time",
        "arr": "array",
        "st": "object",
        "s": "string",
    }
    assert prop(doc, "dec")["physicalType"] == "DECIMAL(10, 2)"


def test_export_writes_row_rates_references_and_unwritable_conditions():
    @sv.transform(
        requires={"orders": REQUIRES},
        ensures=[
            sv.rows_per("customer", at_most=5),
            sv.references("customer", to=("customers", "id")),
            sv.key("id"),
        ],
        on_unproved="check",
    )
    def kept(orders):
        return orders

    doc = valid(odcs.export(orders().pipe(kept)))
    (rate,) = [r for r in doc["schema"][0]["quality"] if r.get("type") == "sql"]
    assert rate["dimension"] == "uniqueness" and rate["mustBe"] == 0
    assert rate["query"] == (
        'SELECT COUNT(*) FROM (SELECT "customer" FROM {object} GROUP BY "customer" '
        "HAVING COUNT(*) > 5)"
    )
    assert prop(doc, "customer")["relationships"] == [{"type": "foreignKey", "to": "customers.id"}]
    # The rate reads back as the same condition.
    back = odcs.read(doc, strict=True).conditions()
    assert any(isinstance(c, RowsPer) and c.cols == ("customer",) and c.n == 5 for c in back)
    assert any(isinstance(c, References) and c.col == "customer" for c in back)
