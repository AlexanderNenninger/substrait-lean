"""The public API (`docs/stability.md`) is the `__all__` of `sverify`,
`sverify.io`, `sverify.engines`, `sverify.types`, `sverify.testing`,
`sverify.errors`, `sverify.cli`, `sverify.odcs` and `sverify.openlineage`,
and the members without an underscore of the classes among them. Every name
in it is documented (a class or function by its own docstring, any other
value in its module's docstring), the API reference lists each, and every
sverify class a public name returns, holds or takes is public too."""

import ast
import functools
import importlib
import inspect
import sys
import typing

import pytest

from _repo import ROOT, needs_repo

PUBLIC = [
    "sverify",
    "sverify.io",
    "sverify.engines",
    "sverify.types",
    "sverify.testing",
    "sverify.errors",
    "sverify.cli",
    "sverify.odcs",
    "sverify.openlineage",
]


def documented(module, name: str) -> bool:
    obj = getattr(module, name)
    if inspect.isclass(obj):
        return bool(obj.__dict__.get("__doc__"))
    if inspect.isfunction(obj):
        return bool(obj.__doc__)
    return f"`{name}`" in (module.__doc__ or "")


@pytest.mark.parametrize("name", PUBLIC)
def test_every_public_name_is_documented(name):
    module = importlib.import_module(name)
    assert module.__doc__, f"{name} has no docstring"
    missing = [n for n in module.__all__ if not documented(module, n)]
    assert not missing, f"{name}: undocumented public names {missing}"


@pytest.mark.parametrize("name", PUBLIC)
def test_all_has_no_duplicates(name):
    names = importlib.import_module(name).__all__
    assert len(set(names)) == len(names)


def test_the_top_level_is_small():
    import sverify as sv

    assert sorted(sv.__all__) == [
        "ContractedTransform",  # what @sv.transform returns, for isinstance (#682)
        "Node",
        "Report",
        "Verdict",
        "approx",
        "arrives_within",
        "asof_join",
        "connect",
        "equivalent",
        "group",
        "key",
        "max_rows",
        "references",
        "rows_per",
        "sql",
        "transform",
        "unique",
        "verify",
        "within",
    ]


UNLISTED = {
    # Deprecated; removed under #1288's decision 5.
    "engines.create_table",
    "engines.table_rows",
    # The OpenLineage client sverify[openlineage] pins, which no event
    # carries; documented in the module's docstring.
    "openlineage.CLIENT_VERSION",
}
"""In an `__all__` and out of the reference."""

EXCLUDED = {
    # Reached only through `Dialect`'s SQL-writing methods, which are
    # outside the promise (`docs/stability.md`).
    "sverify.black_box.BlackBox": "Dialect's SQL-writing methods",
    "sverify.sql.core._base.Dec": "Dialect's SQL-writing methods",
    "sverify.sql.core._base.Lst": "Dialect's SQL-writing methods",
    "sverify.sql.core._base.Unsupported": "Dialect's SQL-writing methods; a deprecated alias",
    # What `Node.write` asks of a sink, as a protocol; `io.Sink` is the
    # public class that implements it.
    "sverify.nodes.Sink": "the protocol io.Sink implements",
    # A `Native` table `run` can return; `Native`'s members are outside the
    # promise while the native scans move into the engine packages.
    "sverify._scan.Resident": "a Native",
}
"""Sverify classes a public name reaches that are not public, with why."""


def _reference() -> list[dict]:
    yaml = pytest.importorskip("yaml")
    return yaml.safe_load((ROOT / "python" / "great-docs.yml").read_text())["reference"]


def _entries(reference: list[dict]) -> list[str | dict]:
    return [c for section in reference for c in section["contents"]]


@needs_repo
def test_the_reference_lists_the_public_api():
    """The reference's table of contents (`great-docs.yml`) and the
    `__all__`s name the same objects (`docs/stability.md`)."""
    toc = {c if isinstance(c, str) else c["name"] for c in _entries(_reference())}
    public = set()
    for name in PUBLIC:
        prefix = "" if name == "sverify" else name.removeprefix("sverify.") + "."
        public |= {prefix + n for n in importlib.import_module(name).__all__}
    assert toc - public == set(), "in the reference, in no __all__"
    assert public - toc == UNLISTED, "in an __all__, not in the reference"


@needs_repo
def test_the_reference_lists_members_that_exist():
    """A `members:` list names attributes of its class, so a rename fails
    here, not in the docs build."""
    for entry in _entries(_reference()):
        if isinstance(entry, dict) and "members" in entry:
            module, _, name = entry["name"].rpartition(".")
            cls = getattr(
                importlib.import_module(f"sverify.{module}" if module else "sverify"), name
            )
            names = set(dir(cls)).union(*(vars(k).get("__annotations__", {}) for k in cls.__mro__))
            assert set(entry["members"]) <= names, entry["name"]


@functools.cache
def _scope(module: str) -> dict:
    """The names an annotation in `module` may use: the module's own, and
    those it imports for type checking only (its `if TYPE_CHECKING:`
    imports, run here; one of a package that is not installed is skipped)."""
    mod = sys.modules[module]
    scope = dict(vars(mod))
    missing: set[str] = set()
    tree = ast.parse(inspect.getsource(mod))
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and ast.unparse(node.test) in (
            "TYPE_CHECKING",
            "_TYPE_CHECKING",
        ):
            for stmt in node.body:
                if isinstance(stmt, (ast.Import, ast.ImportFrom)):
                    try:
                        exec(compile(ast.Module([stmt], []), module, "exec"), scope)  # noqa: S102
                    except ImportError:
                        missing |= {(a.asname or a.name).partition(".")[0] for a in stmt.names}
    scope["__not_installed__"] = missing
    return scope


def _sverify(cls: type) -> bool:
    return cls.__module__.partition(".")[0] == "sverify"


def _resolved(annotations: dict, module: str, where: str, unresolved: set):
    """Each annotation of `annotations` resolved on its own, in `module`'s
    scope (`_scope`); one that cannot be goes to `unresolved` as
    `where.name`."""
    scope = _scope(module)
    for name, hint in annotations.items():
        if isinstance(hint, str):
            try:
                hint = eval(hint, scope)  # noqa: S307 (sverify's own annotations)
            except NameError as e:
                if e.name not in scope["__not_installed__"]:
                    unresolved.add(f"{where}.{name}")
                continue
        yield name, hint


def _function(member):
    """The function behind a method, property or cached property, or None."""
    for attr in ("fget", "func", "__func__"):
        member = getattr(member, attr, member)
    return member if inspect.isfunction(member) else None


def _reached(obj, unresolved: set):
    """The hints of a public function, or of a class's public fields and of
    its public methods' and properties' parameters and returns, inherited
    from its sverify bases too."""
    if inspect.isfunction(obj):
        yield from (
            h
            for _, h in _resolved(obj.__annotations__, obj.__module__, obj.__qualname__, unresolved)
        )
        return
    if not inspect.isclass(obj):
        return
    done: set[str] = set()
    for base in filter(_sverify, obj.__mro__):
        own = vars(base).get("__annotations__", {})
        public = {n: h for n, h in own.items() if not n.startswith("_") and n not in done}
        for _name, hint in _resolved(public, base.__module__, base.__qualname__, unresolved):
            yield hint
        for name, member in vars(base).items():
            f = _function(member)
            if name.startswith("_") or name in done or f is None:
                continue
            done.add(name)
            yield from (
                h for _, h in _resolved(f.__annotations__, f.__module__, f.__qualname__, unresolved)
            )
        done |= set(own)


def _classes(hint):
    if inspect.isclass(hint):
        yield hint
    for arg in typing.get_args(hint):
        if isinstance(arg, (list, tuple)):  # `Callable[[A], B]`'s parameters
            for a in arg:
                yield from _classes(a)
        else:
            yield from _classes(arg)


def test_every_type_a_public_name_reaches_is_public():
    """Closure: a sverify class a public name returns, holds or takes,
    through any number of steps, is in a public `__all__` or in `EXCLUDED`."""
    public = {
        id(getattr(module, n))
        for module in map(importlib.import_module, PUBLIC)
        for n in module.__all__
    }
    todo = [getattr(m, n) for m in map(importlib.import_module, PUBLIC) for n in m.__all__]
    seen: set[int] = set()
    missing = {}
    unresolved: set[str] = set()
    while todo:
        obj = todo.pop()
        if id(obj) in seen:
            continue
        seen.add(id(obj))
        for hint in _reached(obj, unresolved):
            for cls in _classes(hint):
                if not _sverify(cls):
                    continue
                name = f"{cls.__module__}.{cls.__qualname__}"
                if id(cls) not in public and name not in EXCLUDED:
                    missing[name] = obj.__qualname__
                todo.append(cls)
    assert missing == {}, "reached, and in no public __all__ (name: reached from)"
    assert unresolved == set(), "an annotation that names nothing"


def test_verdict_has_no_truth_value():
    """`assert report.verdict` must not pass on UNPROVED: it raises instead."""
    from sverify import Verdict

    for v in Verdict:
        with pytest.raises(TypeError):
            bool(v)
        with pytest.raises(TypeError):
            assert v
