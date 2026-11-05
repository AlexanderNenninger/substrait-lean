"""The file being checked, as text and as a Python AST: positions in the
editor's terms, the subjects sverify checks (`@sv.transform` functions and
`sv.verify` calls), their contracts, and the edits a quick fix makes."""

from __future__ import annotations

import ast
import json
import re
from collections.abc import Iterator
from dataclasses import dataclass, field

#: A range as the editor reads it: start line, start character, end line,
#: end character, 0-based, characters in UTF-16 code units.
Range = tuple[int, int, int, int]

CONTRACT_HELPERS = ("unique", "max_rows", "rows_per", "references", "approx", "arrives_within")


class Source:
    """A Python file, with conversions from the AST's positions."""

    def __init__(self, path: str, text: str):
        self.path, self.text = path, text
        self.lines = text.splitlines(keepends=True) or [""]
        self.tree = ast.parse(text, filename=path)
        self.parents: dict[ast.AST, ast.AST] = {}
        for node in ast.walk(self.tree):
            for child in ast.iter_child_nodes(node):
                self.parents[child] = node
        self.sv = self._alias("sverify", "sv")
        self.has_underscore = any(
            isinstance(n, ast.ImportFrom) and n.module == "ibis" and any(a.name == "_" for a in n.names)
            for n in ast.walk(self.tree)
        )
        self.has_ibis = self._alias("ibis", None) == "ibis"
        self.datetime = self._datetime()

    def _datetime(self) -> str | None:
        """How the file spells the `datetime` class, None if it imports none."""
        for n in ast.walk(self.tree):
            if isinstance(n, ast.ImportFrom) and n.module == "datetime":
                for a in n.names:
                    if a.name == "datetime":
                        return a.asname or "datetime"
        mod = self._alias("datetime", None)
        return f"{mod}.datetime" if mod else None

    def _alias(self, module: str, default: str | None) -> str | None:
        for n in ast.walk(self.tree):
            if isinstance(n, ast.Import):
                for a in n.names:
                    if a.name == module:
                        return a.asname or a.name
        return default

    # -- positions ------------------------------------------------------------

    def char(self, line: int, byte_col: int) -> int:
        """The UTF-16 column of an AST's UTF-8 byte offset on 1-based `line`."""
        raw = self.lines[line - 1].encode()[:byte_col].decode(errors="replace")
        return len(raw.encode("utf-16-le")) // 2

    def range(self, node: ast.AST) -> Range:
        return (
            node.lineno - 1,
            self.char(node.lineno, node.col_offset),
            node.end_lineno - 1,
            self.char(node.end_lineno, node.end_col_offset),
        )

    def line_range(self, line: int) -> Range:
        """The text of 0-based `line`, without its indentation."""
        text = self.lines[line].rstrip("\r\n")
        start = len(text) - len(text.lstrip())
        return (line, start, line, len(text.encode("utf-16-le")) // 2)

    def segment(self, node: ast.AST) -> str:
        return ast.get_source_segment(self.text, node) or ""

    def offset_pos(self, offset: int) -> tuple[int, int]:
        """The (line, UTF-16 character) of a character offset into `text`."""
        before = self.text[:offset]
        line = before.count("\n")
        col = len(before[before.rfind("\n") + 1 :].encode("utf-16-le")) // 2
        return line, col

    def node_offset(self, node: ast.AST) -> int:
        """The character offset of `node`'s start in `text`."""
        start = sum(len(x) for x in self.lines[: node.lineno - 1])
        return start + len(self.lines[node.lineno - 1].encode()[: node.col_offset].decode())

    def indent_of(self, line: int) -> str:
        text = self.lines[line - 1]
        return text[: len(text) - len(text.lstrip())]

    # -- lookups --------------------------------------------------------------

    def module_assign(self, name: str) -> ast.expr | None:
        """The value of a module-level `name = ...` (the last one)."""
        found = None
        for stmt in self.tree.body:
            if isinstance(stmt, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == name for t in stmt.targets
            ):
                found = stmt.value
            elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                if stmt.target.id == name and stmt.value is not None:
                    found = stmt.value
        return found

    def resolve(self, node: ast.expr | None, scope: ast.AST | None = None) -> ast.expr | None:
        """`node`, or for a name the value it was assigned in `scope` or the
        module (one level)."""
        if isinstance(node, ast.Name):
            if scope is not None:
                for n in ast.walk(scope):
                    if isinstance(n, ast.Assign) and any(
                        isinstance(t, ast.Name) and t.id == node.id for t in n.targets
                    ):
                        return n.value
            return self.module_assign(node.id) or node
        return node

    def functions(self) -> dict[str, ast.FunctionDef]:
        return {n.name: n for n in ast.walk(self.tree) if isinstance(n, ast.FunctionDef)}

    def is_sv_call(self, node: ast.AST, name: str) -> bool:
        """`node` is a call of `sv.<name>` (or of `<name>` imported bare)."""
        if not isinstance(node, ast.Call):
            return False
        f = node.func
        if isinstance(f, ast.Attribute) and f.attr == name:
            return isinstance(f.value, ast.Name) and f.value.id in {self.sv, "sverify"}
        return isinstance(f, ast.Name) and f.id == name


@dataclass
class Site:
    """Where a contract is written: one table's `requires` list, or the
    `ensures` list."""

    role: str  # "requires" | "ensures"
    table: str | None
    node: ast.expr  # the list (or the whole requires value when it is no literal)
    items: list[ast.expr] = field(default_factory=list)


@dataclass
class Subject:
    """An `@sv.transform` function or an `sv.verify` call."""

    kind: str  # "transform" | "verify"
    name: str
    node: ast.AST  # the FunctionDef or the Call
    call: ast.Call | None  # the decorator's call, or the verify call
    anchor: ast.AST  # what a diagnostic about the whole subject underlines
    params: list[str] = field(default_factory=list)
    requires: ast.expr | None = None
    ensures: ast.expr | None = None
    body: list[ast.AST] = field(default_factory=list)  # where its expressions are written

    @property
    def lines(self) -> tuple[int, int]:
        return self.node.lineno, self.node.end_lineno


def _keyword(call: ast.Call, name: str, position: int | None) -> ast.expr | None:
    for k in call.keywords:
        if k.arg == name:
            return k.value
    if position is not None and len(call.args) > position:
        return call.args[position]
    return None


def subjects(src: Source) -> list[Subject]:
    """The transforms and verify calls of the file, in source order."""
    out: list[Subject] = []
    funcs = src.functions()
    for node in ast.walk(src.tree):
        if isinstance(node, ast.FunctionDef):
            for dec in node.decorator_list:
                call = dec if isinstance(dec, ast.Call) else None
                target = dec.func if call else dec
                fake = ast.Call(func=target, args=[], keywords=[])
                if src.is_sv_call(call or fake, "transform"):
                    s = Subject(
                        "transform",
                        node.name,
                        node,
                        call,
                        node,
                        [a.arg for a in node.args.args],
                        _keyword(call, "requires", 0) if call else None,
                        _keyword(call, "ensures", 1) if call else None,
                    )
                    s.body = [node, *_called(node, funcs)]
                    out.append(s)
        elif src.is_sv_call(node, "verify"):
            arg = node.args[0] if node.args else _keyword(node, "transform", None)
            body: list[ast.AST] = []
            if arg is not None:
                body.append(arg)
                if isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name):
                    fn = funcs.get(arg.func.id)
                    if fn is not None:
                        body += [fn, *_called(fn, funcs)]
                resolved = src.resolve(arg)
                if resolved is not arg and resolved is not None:
                    body.append(resolved)
            parent = src.parents.get(node)
            name = "verify"
            if isinstance(parent, ast.Assign) and isinstance(parent.targets[0], ast.Name):
                name = parent.targets[0].id
            out.append(
                Subject(
                    "verify",
                    name,
                    node,
                    node,
                    node.func,
                    [],
                    _keyword(node, "requires", None),
                    _keyword(node, "ensures", None),
                    body,
                )
            )
    out.sort(key=lambda s: (s.node.lineno, s.node.col_offset))
    return out


def _called(fn: ast.FunctionDef, funcs: dict[str, ast.FunctionDef]) -> list[ast.FunctionDef]:
    """The module's functions `fn` calls, transitively (where a transform's
    body is a helper, as in the tour)."""
    seen: list[ast.FunctionDef] = []
    todo = [fn]
    while todo:
        f = todo.pop()
        for n in ast.walk(f):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
                g = funcs.get(n.func.id)
                if g is not None and g is not fn and g not in seen:
                    seen.append(g)
                    todo.append(g)
    return seen


def sites(src: Source, s: Subject, tables: list[str]) -> list[Site]:
    """The contract's lists: one per table of `requires`, and `ensures`."""
    scope = s.node if s.kind == "transform" else None
    out = []
    req = src.resolve(s.requires, scope)
    if isinstance(req, ast.Dict):
        for k, v in zip(req.keys, req.values, strict=True):
            if isinstance(k, ast.Constant) and isinstance(k.value, str):
                v = src.resolve(v, scope)
                items = list(v.elts) if isinstance(v, (ast.List, ast.Tuple)) else []
                out.append(Site("requires", k.value, v, items))
    elif isinstance(req, (ast.List, ast.Tuple)):
        table = tables[0] if len(tables) == 1 else None
        out.append(Site("requires", table, req, list(req.elts)))
    ens = src.resolve(s.ensures, scope)
    if isinstance(ens, (ast.List, ast.Tuple)):
        out.append(Site("ensures", None, ens, list(ens.elts)))
    return out


# -- finding an expression the report names ------------------------------------

#: Ibis methods for the SQL functions a report names (`sum(x)` is `_.x.sum()`).
_METHODS = {
    "avg": {"mean"},
    "mean": {"mean"},
    "sum": {"sum"},
    "count": {"count"},
    "min": {"min"},
    "max": {"max"},
    "abs": {"abs"},
    "sqrt": {"sqrt"},
    "ln": {"ln", "log"},
    "log": {"log", "log10", "ln"},
    "pow": {"pow"},
}

_OPS = {
    ast.Div: "/",
    ast.FloorDiv: "//",
    ast.Mod: "%",
    ast.Mult: "*",
    ast.Add: "+",
    ast.Sub: "-",
    ast.Pow: "**",
}


def column_name(node: ast.AST) -> str | None:
    """The column an Ibis expression names: `t.x`, `_.x`, `t["x"]`, `x`."""
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
        if node.func.attr in {"over", "cast", "fill_null", "coalesce"}:
            return column_name(node.func.value)
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Constant):
        return node.slice.value if isinstance(node.slice.value, str) else None
    if isinstance(node, ast.Name):
        return node.id
    return None


def _same(pattern: ast.AST, node: ast.AST) -> bool:
    if isinstance(pattern, ast.Name):
        return column_name(node) == pattern.id
    if isinstance(pattern, ast.Constant):
        return isinstance(node, ast.Constant) and node.value == pattern.value
    if isinstance(pattern, ast.UnaryOp) and isinstance(node, ast.UnaryOp):
        return type(pattern.op) is type(node.op) and _same(pattern.operand, node.operand)
    if isinstance(pattern, ast.BinOp) and isinstance(node, ast.BinOp):
        return _match_binop(pattern, node, strict=True)
    return False


def _match_binop(pattern: ast.BinOp, node: ast.BinOp, strict: bool) -> bool:
    ops = {type(pattern.op)}
    if not strict and isinstance(pattern.op, (ast.Div, ast.FloorDiv)):
        ops = {ast.Div, ast.FloorDiv}
    return type(node.op) in ops and _same(pattern.left, node.left) and _same(pattern.right, node.right)


def find_expr(src: Source, shown: str, regions: list[ast.AST]) -> tuple[ast.AST | None, Range | None]:
    """Where `shown` (`Issue.shown`: column names and the Ibis or SQL
    operator, `total // qty`, `sum(x)`) is written in `regions`, then in the
    whole file: an AST node of Ibis code, or a range inside a SQL string."""
    try:
        pattern = ast.parse(shown, mode="eval").body
    except SyntaxError:
        pattern = None
    for region in [*regions, src.tree]:
        nodes = list(ast.walk(region))
        if pattern is not None:
            for strict in (True, False):
                for n in nodes:
                    if isinstance(pattern, ast.BinOp) and isinstance(n, ast.BinOp):
                        if _match_binop(pattern, n, strict):
                            return n, src.range(n)
            if isinstance(pattern, ast.Call) and isinstance(pattern.func, ast.Name) and pattern.args:
                methods = _METHODS.get(pattern.func.id.lower(), {pattern.func.id.lower()})
                for n in nodes:
                    if (
                        isinstance(n, ast.Call)
                        and isinstance(n.func, ast.Attribute)
                        and n.func.attr in methods
                        and _same(pattern.args[0], n.func.value)
                    ):
                        return n, src.range(n)
        hit = _in_sql(src, shown, nodes)
        if hit is not None:
            return None, hit
        if isinstance(pattern, ast.Name):
            for n in nodes:
                if isinstance(n, ast.Attribute) and n.attr == pattern.id:
                    return n, src.range(n)
    return None, None


def _sql_regex(shown: str) -> re.Pattern[str]:
    parts = []
    for tok in re.findall(r"\w+|//|\*\*|\S", shown):
        if re.fullmatch(r"[A-Za-z_]\w*", tok):
            parts.append(r"(?:\w+\.)?\"?" + re.escape(tok) + r"\"?")
        elif tok == "//":
            parts.append(r"(?://|/)")
        else:
            parts.append(re.escape(tok))
    return re.compile(r"\s*".join(parts), re.IGNORECASE)


def sql_strings(nodes: list[ast.AST]) -> Iterator[ast.Constant]:
    for n in nodes:
        if (
            isinstance(n, ast.Constant)
            and isinstance(n.value, str)
            and re.search(r"\bselect\b", n.value, re.IGNORECASE)
        ):
            yield n


def _in_sql(src: Source, shown: str, nodes: list[ast.AST]) -> Range | None:
    rx = _sql_regex(shown)
    for n in sql_strings(nodes):
        raw = src.segment(n)
        m = rx.search(raw)
        if m:
            base = src.node_offset(n)
            return (*src.offset_pos(base + m.start()), *src.offset_pos(base + m.end()))
    return None


# -- edits ----------------------------------------------------------------------


@dataclass
class Edit:
    range: Range
    text: str

    def json(self) -> dict:
        return {"range": list(self.range), "newText": self.text}


def strip_parens(label: str) -> str:
    """A condition's label without the parentheses Ibis puts around it."""
    if label.startswith("(") and label.endswith(")"):
        depth = 0
        for i, ch in enumerate(label):
            depth += ch == "("
            depth -= ch == ")"
            if depth == 0 and i < len(label) - 1:
                return label
        return label[1:-1]
    return label


def label_code(label: str, sv: str, dt: str | None = "datetime") -> str:
    """Python code for a condition label of a report or route suggestion;
    `dt` spells the `datetime` class as the file does."""
    if dt and dt != "datetime":
        label = re.sub(r"(?<![\w.])datetime(?:\.datetime)?\(", dt + "(", label)
    m = re.fullmatch(r"unique\((.*)\)", label)
    if m:
        return f"{sv}.unique({', '.join(_q(c.strip()) for c in m[1].split(','))})"
    m = re.fullmatch(r"(max_rows|rows_per|references|arrives_within)\((.*)\)", label)
    if m:
        return f"{sv}.{label}"
    if label.startswith("(_") or label.startswith("_.") or label.startswith("~_"):
        return strip_parens(label)
    if label.startswith(f"{sv}."):
        return label
    return _q(label)


def _q(text: str) -> str:
    """A Python string literal in double quotes."""
    return json.dumps(text, ensure_ascii=False)


def insert_items(src: Source, lst: ast.expr, codes: list[str]) -> Edit:
    """Append `codes` to a list literal, in its layout."""
    assert isinstance(lst, (ast.List, ast.Tuple))
    end_line = lst.end_lineno
    if not lst.elts:
        r = src.range(lst)
        return Edit(r, "[" + ", ".join(codes) + "]")
    last = lst.elts[-1]
    if last.end_lineno != end_line:  # one item per line
        return _after_last(src, last, [f"{c}," for c in codes], src.indent_of(last.lineno))
    ch = src.char(last.end_lineno, last.end_col_offset)
    line = last.end_lineno - 1
    return Edit((line, ch, line, ch), "".join(f", {c}" for c in codes))


def _after_last(src: Source, last: ast.AST, lines: list[str], indent: str) -> Edit:
    """New lines after `last`, the last item of a list or dict laid out one
    item per line, and after its trailing comma where it has one."""
    line = last.end_lineno
    rest = src.lines[line - 1].encode()[last.end_col_offset :].decode()
    col = last.end_col_offset
    text = "".join(f"\n{indent}{x}" for x in lines)
    if rest.lstrip().startswith(","):
        col += len((rest[: len(rest) - len(rest.lstrip())] + ",").encode())
    else:
        text = "," + text
    ch = src.char(line, col)
    return Edit((line - 1, ch, line - 1, ch), text)


def add_requires(src: Source, s: Subject, table: str, codes: list[str], tables: list[str]) -> Edit | None:
    """The edit that states `codes` in the `requires` of `table`."""
    scope = s.node if s.kind == "transform" else None
    req = src.resolve(s.requires, scope)
    if isinstance(req, ast.Dict):
        for k, v in zip(req.keys, req.values, strict=True):
            if isinstance(k, ast.Constant) and k.value == table:
                v = src.resolve(v, scope)
                if isinstance(v, (ast.List, ast.Tuple)):
                    return insert_items(src, v, codes)
                return None
        entry = f"{_q(table)}: [{', '.join(codes)}]"
        if not req.values:
            return Edit(src.range(req), "{" + entry + "}")
        last = req.values[-1]
        if last.end_lineno != req.end_lineno:
            return _after_last(src, last, [f"{entry},"], src.indent_of(req.keys[-1].lineno))
        ch = src.char(last.end_lineno, last.end_col_offset)
        return Edit((last.end_lineno - 1, ch, last.end_lineno - 1, ch), f", {entry}")
    if isinstance(req, (ast.List, ast.Tuple)) and len(tables) <= 1:
        return insert_items(src, req, codes)
    if s.requires is None and s.call is not None:
        value = (
            f"[{', '.join(codes)}]"
            if s.kind == "transform" and len(tables) == 1
            else ("{" + f"{_q(table)}: [{', '.join(codes)}]" + "}")
        )
        call = s.call
        ens = next((k for k in call.keywords if k.arg == "ensures"), None)
        if ens is not None:  # requires= before ensures=
            ch = src.char(ens.lineno, ens.col_offset)
            return Edit((ens.lineno - 1, ch, ens.lineno - 1, ch), f"requires={value}, ")
        # after the last argument, or right after "(".
        args = [*call.args, *call.keywords]
        if args:
            last = max(args, key=lambda a: (a.end_lineno, a.end_col_offset))
            ch = src.char(last.end_lineno, last.end_col_offset)
            return Edit((last.end_lineno - 1, ch, last.end_lineno - 1, ch), f", requires={value}")
        ch = src.char(call.end_lineno, call.end_col_offset) - 1
        return Edit((call.end_lineno - 1, ch, call.end_lineno - 1, ch), f"requires={value}")
    if s.requires is None and s.call is None and s.kind == "transform":
        dec = next(d for d in s.node.decorator_list)
        ch = src.char(dec.end_lineno, dec.end_col_offset)
        value = (
            f"[{', '.join(codes)}]" if len(tables) == 1 else "{" + f"{_q(table)}: [{', '.join(codes)}]" + "}"
        )
        return Edit((dec.end_lineno - 1, ch, dec.end_lineno - 1, ch), f"(requires={value})")
    return None


def import_datetime(src: Source) -> Edit | None:
    """`from datetime import datetime`, where the file imports no datetime."""
    if src.datetime:
        return None
    line = 0
    for stmt in src.tree.body:
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            line = stmt.lineno - 1
            break
    return Edit((line, 0, line, 0), "from datetime import datetime\n")


def import_underscore(src: Source) -> Edit | None:
    """`from ibis import _`, where the file lacks it."""
    if src.has_underscore:
        return None
    line = 0
    for stmt in src.tree.body:
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            line = stmt.end_lineno
    return Edit((line, 0, line, 0), "from ibis import _\n")
