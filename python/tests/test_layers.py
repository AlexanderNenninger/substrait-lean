"""Sverify's modules import each other in one order (#730).

`LAYERS` lists them from the bottom up; `docs/layers.md` says what each layer
is for. A module imports from its own layer or the ones below it, at the top
of the file or inside a function, and the imports inside a layer form no
cycle. Imports under `if TYPE_CHECKING:` are for annotations only and may go
anywhere.
"""

import ast
from pathlib import Path

import sverify

SRC = Path(sverify.__file__).resolve().parent

#: The layers, bottom first. A name is a module or a package of `sverify`.
LAYERS: list[tuple[str, list[str]]] = [
    (
        "base",
        [
            "_meta",
            "_deprecated",
            "_duration",
            "_stages",
            "_cursor",
            "_unsupported",
            "_plan_read",
            "_user_text",
            "_functions",
            "black_box",
            "_engines",
            "_support",
            "plan_json",
            "_duckdb",
            "_scan",
            "_decimals",
            "_proof_cache",
            "_checker",
            "_lean_eval",
            "_weighted",
            "_hooks",
            "_pipe",
            "profiles",
        ],
    ),
    ("frontends", ["ibis_substrait", "sql_lift"]),
    (
        "writers and engines",
        ["sql", "duckdb_engine"],
    ),
    ("checker", ["engine", "_engine_settings", "_builtin"]),
    ("conditions", ["observation", "counterexample", "conditions", "_quarantine"]),
    (
        "report",
        ["routes", "report", "_verdict", "report_json", "substrait_export", "_substrait_shims"],
    ),
    ("transform", ["contracts"]),
    (
        "incremental",
        ["_state", "_retention", "_exact_sum", "_linear", "_semi", "_touched", "incremental"],
    ),
    ("io", ["io"]),
    ("nodes", ["steps", "nodes", "sql_model", "partition", "asof"]),
    ("integrations", ["odcs", "openlineage"]),
    ("public", ["cli", "testing", "pytest_plugin", "display", "engines", "errors", "sverify"]),
]


def _layer_of() -> dict[str, int]:
    return {name: i for i, (_, names) in enumerate(LAYERS) for name in names}


def _modules() -> dict[str, Path]:
    mods = {}
    for p in SRC.rglob("*.py"):
        parts = list(p.relative_to(SRC.parent).with_suffix("").parts)
        if parts[-1] == "__init__":
            parts.pop()
        mods[".".join(parts)] = p
    return mods


MODULES = _modules()


def _unit(module: str) -> str:
    """The `LAYERS` name a module belongs to."""
    if module == "sverify":
        return "sverify"
    return module.split(".")[1]


def _targets(module: str, node: ast.Import | ast.ImportFrom) -> list[str]:
    if isinstance(node, ast.Import):
        names = [a.name for a in node.names]
    else:
        base = module.split(".")
        if node.level:
            is_pkg = MODULES[module].name == "__init__.py"
            base = base[: len(base) - node.level + (1 if is_pkg else 0)]
            target = ".".join(base + ([node.module] if node.module else []))
        else:
            target = node.module or ""
        names = [f"{target}.{a.name}" for a in node.names]
    out = []
    for name in names:
        if not (name == "sverify" or name.startswith("sverify.")):
            continue
        while name not in MODULES and "." in name:
            name = name.rsplit(".", 1)[0]
        out.append(name)
    return out


def _imports() -> list[tuple[str, str, int, bool]]:
    """Every import of a sverify module by another: (from, to, line, inside a function)."""
    edges = []

    def walk(module: str, node: ast.AST, in_function: bool) -> None:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.If) and "TYPE_CHECKING" in ast.unparse(child.test):
                for c in child.orelse:
                    walk(module, c, in_function)
                continue
            if isinstance(child, ast.Import | ast.ImportFrom):
                for target in _targets(module, child):
                    if target != module:
                        edges.append((module, target, child.lineno, in_function))
            walk(
                module,
                child,
                in_function or isinstance(child, ast.FunctionDef | ast.AsyncFunctionDef),
            )

    for module, path in MODULES.items():
        walk(module, ast.parse(path.read_text()), False)
    return edges


IMPORTS = _imports()


def _where(module: str, line: int) -> str:
    return f"{MODULES[module].relative_to(SRC.parent)}:{line}"


def test_every_module_has_a_layer():
    layer = _layer_of()
    assert len(layer) == sum(len(names) for _, names in LAYERS), "a name is listed twice"
    unplaced = sorted({_unit(m) for m in MODULES} - set(layer))
    assert not unplaced, f"add these to a layer in LAYERS: {unplaced}"
    gone = sorted(set(layer) - {_unit(m) for m in MODULES})
    assert not gone, f"LAYERS names modules that do not exist: {gone}"


def test_imports_go_down():
    layer = _layer_of()
    up = [
        f"{_where(a, line)}: {a} ({LAYERS[layer[_unit(a)]][0]}) imports {b} "
        f"({LAYERS[layer[_unit(b)]][0]})"
        for a, b, line, _ in IMPORTS
        if layer[_unit(b)] > layer[_unit(a)]
    ]
    assert not up, "imports against the order of LAYERS:\n" + "\n".join(up)


def test_no_cycles():
    graph: dict[str, set[str]] = {}
    for a, b, _, _ in IMPORTS:
        if a.startswith(b + "."):
            continue  # a package's module reads its own `__init__`
        graph.setdefault(a, set()).add(b)
    cycles = []
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(m: str) -> None:
        state[m] = 1
        stack.append(m)
        for n in sorted(graph.get(m, ())):
            if state.get(n) == 1:
                cycles.append(" -> ".join([*stack[stack.index(n) :], n]))
            elif n not in state:
                visit(n)
        stack.pop()
        state[m] = 2

    for m in sorted(graph):
        if m not in state:
            visit(m)
    assert not cycles, "import cycles:\n" + "\n".join(cycles)
