"""`sverify suggest`: write the preconditions a proof needs
(`Report.needs`) into the `requires=` of each transform's decorator (#744)."""

from __future__ import annotations

import ast
import inspect
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sverify.cli._discover import Checked
    from sverify.contracts import Needed


@dataclass
class Fix:
    """The preconditions one transform needs, per parameter, as the code
    `requires=` takes, and whether `apply` could place them."""

    transform: str
    conditions: dict[str, list[str]]
    placed: bool = False
    reason: str | None = None


@dataclass
class Plan:
    fixes: list[Fix] = field(default_factory=list)
    text: str | None = None
    """The file with the fixes placed, if any were."""


def condition_code(n: Needed, dialect: str) -> str:
    """`n` as the code a `requires=` list takes: the Python of an Ibis
    condition, NULL passing where its SQL lets it, or the SQL as a string
    for a SQL transform."""
    if dialect != "ibis" or n.column is None or n.op is None:
        return repr(n.sql)
    nulls = '"' + n.column.replace('"', '""') + '" IS NULL OR '
    if n.sql.startswith(nulls) and n.op != "IS NOT NULL":
        return f"_.{n.column}.isnull() | ({n.code})"
    return n.code


def fixes(checked: list[Checked]) -> list[Fix]:
    """The fixes each transform needs, one per transform, from every
    application's `Report.needs`."""
    out: dict[int, Fix] = {}
    for c in checked:
        if c.report is None or not c.report.needs:
            continue
        fix = out.setdefault(id(c.transform), Fix(c.name, {}))
        for n in c.report.needs:
            param = c.params.get(n.table, n.table)
            code = condition_code(n, c.report.dialect)
            codes = fix.conditions.setdefault(param, [])
            if code not in codes:
                codes.append(code)
    return list(out.values())


def place(path: Path, checked: list[Checked]) -> Plan:
    """The file at `path` with each transform's needed preconditions added
    to its decorator's `requires=`."""
    plan = Plan(fixes(checked))
    if not plan.fixes:
        return plan
    source = path.read_bytes()
    tree = ast.parse(source)
    lines = source.splitlines(keepends=True)
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line))

    def at(lineno: int, col: int) -> int:
        return starts[lineno - 1] + col

    transforms = {id(c.transform): c.transform for c in checked}
    edits: list[tuple[int, int, str]] = []
    uses_underscore = False
    for fix in plan.fixes:
        t = next(t for t in transforms.values() if t.name == fix.transform)
        call = _decorator(tree, t)
        if call is None:
            fix.reason = f"no @transform(...) decorator of {fix.transform} in {path.name}"
            continue
        edit = _requires_edit(call, fix.conditions, at, len(inspect.signature(t.fn).parameters))
        if isinstance(edit, str):
            fix.reason = edit
            continue
        edits += edit
        fix.placed = True
        uses_underscore |= any(c.startswith("_.") for cs in fix.conditions.values() for c in cs)
    if not edits:
        return plan
    if uses_underscore and not _imports_underscore(tree):
        edits.append(_import_edit(tree, at))
    out = source
    for start, end, text in sorted(edits, key=lambda e: (e[0], e[1]), reverse=True):
        out = out[:start] + text.encode() + out[end:]
    plan.text = out.decode()
    return plan


def _decorator(tree: ast.Module, t: object) -> ast.Call | None:
    fn = getattr(t, "fn", None)
    name = getattr(fn, "__name__", None)
    first = getattr(getattr(fn, "__code__", None), "co_firstlineno", None)
    found: list[tuple[bool, ast.Call]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef) and node.name == name:
            for d in node.decorator_list:
                if not isinstance(d, ast.Call):
                    continue
                f = d.func
                if (getattr(f, "attr", None) or getattr(f, "id", None)) == ("transform"):
                    lines = {node.lineno, *(x.lineno for x in node.decorator_list)}
                    found.append((first in lines, d))
    found.sort(key=lambda f: not f[0])
    return found[0][1] if found else None


def _key(param: str) -> str:
    return json.dumps(param)


def _seq(codes: list[str]) -> str:
    return ", ".join(codes)


def _requires_edit(call: ast.Call, conds: dict[str, list[str]], at, n_params: int):
    kw = next((k for k in call.keywords if k.arg == "requires"), None)
    value = kw.value if kw is not None else (call.args[0] if call.args else None)
    if value is None:
        text = "{" + ", ".join(f"{_key(p)}: [{_seq(cs)}]" for p, cs in conds.items()) + "}"
        if call.keywords:
            first = call.keywords[0]
            pos = at(first.lineno, first.col_offset)
            return [(pos, pos, f"requires={text}, ")]
        end = at(call.end_lineno, call.end_col_offset) - 1
        return [(end, end, f"requires={text}")]
    if isinstance(value, ast.List | ast.Tuple):
        if n_params != 1 or len(conds) != 1:
            return "requires= is a list, but the conditions are on several inputs"
        return [_append(value, next(iter(conds.values())), at)]
    if not isinstance(value, ast.Dict):
        return "requires= is not a literal dict or list: add the conditions by hand"
    edits = []
    keys = {
        k.value: v
        for k, v in zip(value.keys, value.values, strict=True)
        if isinstance(k, ast.Constant) and isinstance(k.value, str)
    }
    missing = []
    for param, codes in conds.items():
        v = keys.get(param)
        if v is None:
            missing.append(f"{_key(param)}: [{_seq(codes)}]")
        elif isinstance(v, ast.List | ast.Tuple):
            edits.append(_append(v, codes, at))
        else:
            return f"requires[{param!r}] is not a literal list: add the conditions by hand"
    if missing:
        end = at(value.end_lineno, value.end_col_offset) - 1
        sep = ", " if value.keys else ""
        edits.append((end, end, sep + ", ".join(missing)))
    return edits


def _append(seq: ast.List | ast.Tuple, codes: list[str], at) -> tuple[int, int, str]:
    if seq.elts:
        last = seq.elts[-1]
        pos = at(last.end_lineno, last.end_col_offset)
        return (pos, pos, ", " + _seq(codes))
    end = at(seq.end_lineno, seq.end_col_offset) - 1
    return (end, end, _seq(codes))


def _imports_underscore(tree: ast.Module) -> bool:
    return any(
        isinstance(n, ast.ImportFrom)
        and n.module == "ibis"
        and any(a.name == "_" and a.asname is None for a in n.names)
        for n in tree.body
    )


def _import_edit(tree: ast.Module, at) -> tuple[int, int, str]:
    imports = [n for n in tree.body if isinstance(n, ast.Import | ast.ImportFrom)]
    if imports:
        last = imports[-1]
        pos = at(last.end_lineno, last.end_col_offset)
        return (pos, pos, "\nfrom ibis import _")
    return (0, 0, "from ibis import _\n")
