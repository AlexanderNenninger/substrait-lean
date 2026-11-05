"""The checker on the demo workspace: findings, their places, and quick
fixes that leave valid code which then proves.

    cd vscode && ../python/.venv/bin/python -m pytest python/tests
"""

from __future__ import annotations

import ast
import shutil
from pathlib import Path

import pytest

from sverify_vscode.check import check
from sverify_vscode.source import Source, add_requires, find_expr, label_code, subjects

DEMO = Path(__file__).parents[2] / "demo"


def apply(text: str, edits: list[dict]) -> str:
    """Apply the client's edits (UTF-16 ranges) to `text`."""

    def offset(line: int, ch: int) -> int:
        lines = text.splitlines(keepends=True)
        head = sum(len(x) for x in lines[:line])
        return (
            head + len(lines[line].encode("utf-16-le")[: ch * 2].decode("utf-16-le"))
            if line < len(lines)
            else len(text)
        )

    for e in sorted(edits, key=lambda e: tuple(e["range"][:2]), reverse=True):
        a, b = offset(*e["range"][:2]), offset(*e["range"][2:])
        text = text[:a] + e["newText"] + text[b:]
    return text


@pytest.fixture(scope="module")
def orders() -> dict:
    return check(str(DEMO / "orders.py"), 0)


def by(result: dict, name: str) -> tuple[int, dict]:
    return next((i, s) for i, s in enumerate(result["subjects"]) if s["name"] == name)


def diags(result: dict, name: str, code: str | None = None) -> list[dict]:
    i, _ = by(result, name)
    return [d for d in result["diagnostics"] if d["subject"] == i and (code is None or d["code"] == code)]


def text_at(path: Path, r: list[int]) -> str:
    lines = path.read_text().splitlines()
    assert r[0] == r[2]
    return lines[r[0]][r[1] : r[3]]


def test_statuses(orders):
    status = {s["name"]: s.get("proved") for s in orders["subjects"]}
    assert status == {
        "doubled": True,
        "plus_one": False,
        "unit_price": False,
        "by_id": False,
        "typo": None,  # the contract raised: not checked
        "per_customer": True,
        "unit_price_sql": False,
        "wrong_table": None,  # its decorator raised: the file stopped there
    }


def test_places(orders):
    path = DEMO / "orders.py"
    [needs] = [d for d in diags(orders, "unit_price", "needs") if "qty" in d["message"]]
    assert text_at(path, needs["range"]) == "orders.amount // orders.qty"
    [unproved] = diags(orders, "plus_one", "not-proved")
    assert text_at(path, unproved["range"]) == "_.total > 5"
    [typo] = diags(orders, "typo", "unknown-column")
    assert text_at(path, typo["range"]) == "amout"
    [assumed] = diags(orders, "per_customer", "assumed")
    assert text_at(path, assumed["range"]) == "_.amount.sum()"


def test_hovers_and_lenses(orders):
    i, s = by(orders, "doubled")
    assert "duckdb" in s["routes"] and s["routes"]["duckdb"]["cls"] == "exact"
    lens = next(lens for lens in orders["lenses"] if lens["subject"] == i)
    assert lens["title"].startswith("sverify ✓ proved")
    path = DEMO / "orders.py"
    col = [
        h for h in orders["hovers"] if text_at(path, h["range"]) == "doubled" and "output of" in h["markdown"]
    ]
    assert col and "an integer in [22, 1999999998]" in col[0]["markdown"]


def test_every_fix_parses(orders):
    text = (DEMO / "orders.py").read_text()
    n = 0
    for d in orders["diagnostics"]:
        for f in d["fixes"]:
            ast.parse(apply(text, f["edits"]))
            n += 1
    assert n >= 8


@pytest.mark.parametrize(
    ("name", "code", "title"),
    [
        ("by_id", "not-proved", 'Add sv.unique("id") to requires of orders'),
        ("typo", "unknown-column", "Change to `amount`"),
    ],
)
def test_fix_proves(orders, tmp_path, name, code, title):
    text = (DEMO / "orders.py").read_text()
    [fix] = [f for d in diags(orders, name, code) for f in d["fixes"] if f["title"].startswith(title)]
    fixed = tmp_path / "orders.py"
    fixed.write_text(apply(text, fix["edits"]))
    after = check(str(fixed), 0)
    assert by(after, name)[1]["proved"] is True


def test_assumed_sum_shows_its_hint(orders):
    """The SUM's bounds and row cap are prose only (UX-NOTES, "Public API
    gaps"): the diagnostic shows the hint, and offers no fix."""
    [d] = diags(orders, "per_customer", "assumed")
    assert "hint: SUM of `amount`" in d["message"] and not d["fixes"]


def test_needs_fixes_prove_together(orders, tmp_path):
    """unit_price: the precondition for `//` and the one for NULL qty."""
    text = (DEMO / "orders.py").read_text()
    [fix] = [
        f
        for d in diags(orders, "unit_price", "needs")
        for f in d["fixes"]
        if f["title"].startswith("Add _.qty != 0")
    ]
    fixed = tmp_path / "orders.py"
    fixed.write_text(apply(text, fix["edits"]))
    after = check(str(fixed), 0)
    assert not diags(after, "unit_price", "needs")


def test_guard_fix(orders, tmp_path):
    text = (DEMO / "orders.py").read_text()
    [fix] = [
        f for d in diags(orders, "unit_price", "needs") for f in d["fixes"] if f["title"].startswith("Guard")
    ]
    new = apply(text, fix["edits"])
    assert "ibis.ifelse(orders.qty != 0, orders.amount // orders.qty, None)" in new
    fixed = tmp_path / "orders.py"
    fixed.write_text(new)
    after = check(str(fixed), 0)
    assert not [d for d in diags(after, "unit_price", "needs") if "qty != 0" in d["message"]]


def test_ties_fix(tmp_path):
    shutil.copy(DEMO / "sensors.py", tmp_path / "sensors.py")
    path = tmp_path / "sensors.py"
    result = check(str(path), 0)
    [ties] = diags(result, "unkeyed", "ties")
    [fix] = ties["fixes"][:1]
    new = apply(path.read_text(), fix["edits"])
    assert 'requires={"readings": [sv.unique("device_id", "ts")]}, ensures=' in new
    path.write_text(new)
    after = check(str(path), 0)
    assert not diags(after, "unkeyed", "ties")


def test_sql(tmp_path):
    result = check(str(DEMO / "mart.py"), 0)
    [needs] = diags(result, "sql_report", "needs")
    [fix] = needs["fixes"][:1]
    new = apply((DEMO / "mart.py").read_text(), fix["edits"])
    assert "_.order_ts >= dt.datetime(1, 1, 1)" in new  # the file's `import datetime as dt`
    ast.parse(new)


def test_add_requires_layouts():
    text = """import sverify as sv
from ibis import _

REQ = {
    "orders": [
        sv.unique("id"),
    ],
}


@sv.transform(requires=REQ, ensures=[])
def f(orders):
    return orders


@sv.transform(ensures=[_.x > 0])
def g(orders, other):
    return orders
"""
    src = Source("t.py", text)
    f, g = subjects(src)
    e = add_requires(src, f, "orders", ["_.x > 0"], ["orders"])
    assert apply(text, [e.json()]).count('        sv.unique("id"),\n        _.x > 0,\n') == 1
    e = add_requires(src, f, "other", ["_.y > 0"], ["orders", "other"])
    assert '    "other": [_.y > 0],\n}' in apply(text, [e.json()])
    e = add_requires(src, g, "other", ["_.y > 0"], ["orders", "other"])
    assert '@sv.transform(requires={"other": [_.y > 0]}, ensures=[_.x > 0])' in apply(text, [e.json()])


def test_find_expr():
    text = '''import sverify as sv
Q = """select a / b as r, sum(o.x) as s from t o"""
def f(t):
    return t.select(r=t.a // t.b, m=t.x.mean())
'''
    src = Source("t.py", text)
    node, rng = find_expr(src, "a // b", [src.tree.body[-1]])
    assert ast.unparse(node) == "t.a // t.b"
    node, rng = find_expr(src, "avg(x)", [src.tree.body[-1]])
    assert ast.unparse(node) == "t.x.mean()"
    node, rng = find_expr(src, "sum(x)", [src.tree.body[1]])
    assert node is None and text.splitlines()[rng[0]][rng[1] : rng[3]] == "sum(o.x)"


def test_label_code():
    assert label_code("unique(a, b)", "sv") == 'sv.unique("a", "b")'
    assert label_code("max_rows(10)", "sv") == "sv.max_rows(10)"
    assert label_code("(_.x != 0)", "sv") == "_.x != 0"
    assert label_code("(_.a > 0) & (_.b > 0)", "sv") == "(_.a > 0) & (_.b > 0)"
    assert label_code("a > 0", "sv") == '"a > 0"'
    assert label_code("(_.t >= datetime(1, 1, 1))", "sv", "dt.datetime") == "_.t >= dt.datetime(1, 1, 1)"


def test_sql_guard(orders):
    path = DEMO / "orders.py"
    [needs] = diags(orders, "unit_price_sql", "needs")
    assert text_at(path, needs["range"]) == "amount // qty"
    [fix] = [f for f in needs["fixes"] if f["title"].startswith("Guard")]
    assert 'sv.sql("select id, CASE WHEN qty <> 0 THEN amount // qty END as unit' in apply(
        path.read_text(), fix["edits"]
    )


def test_unknown_table(orders):
    [d] = [d for d in orders["diagnostics"] if d["code"] == "unknown-table"]
    assert text_at(DEMO / "orders.py", d["range"]) == '"order"'
    assert d["fixes"][0]["edits"][0]["newText"] == '"orders"'
