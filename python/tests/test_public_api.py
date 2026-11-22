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
import itertools
import re
import sys
import textwrap
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

#: Documented modules outside the 1.x promise (#881 1.6): their names are in
#: the API reference under a heading that says so, and in no public module.
OUTSIDE = ["sverify.engines.plan"]


def documented(module, name: str) -> bool:
    obj = getattr(module, name)
    if inspect.isclass(obj):
        return bool(obj.__dict__.get("__doc__"))
    if inspect.isfunction(obj):
        return bool(obj.__doc__)
    return f"`{name}`" in (module.__doc__ or "")


@pytest.mark.parametrize("name", PUBLIC + OUTSIDE)
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
        "non_overlapping",
        "references",
        "rows_per",
        "sql",
        "transform",
        "unique",
        "verify",
        "within",
    ]


UNLISTED: set[str] = set()
"""In an `__all__` and out of the reference."""

EXCLUDED = {
    # Reached only through `Dialect`'s SQL-writing methods, which are
    # outside the promise (`docs/stability.md`).
    "sverify.black_box.BlackBox": "Dialect's SQL-writing methods",
    "sverify.sql.core._base.Dec": "Dialect's SQL-writing methods",
    "sverify.sql.core._base.Lst": "Dialect's SQL-writing methods",
    "sverify.sql.core._base.Unsupported": "Dialect's SQL-writing methods: the writer's refusal",
    # A `Native` table `run_plan(keep=True)` returns. It goes with the
    # exception in `docs/stability.md` that keeps `Native`'s members outside
    # the promise while the native scans move into the engine packages.
    "sverify._scan.Resident": "a Native, under Native's stability exception",
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
    outside = {
        name.removeprefix("sverify.") + "." + n
        for name in OUTSIDE
        for n in importlib.import_module(name).__all__
    }
    assert toc - public == outside, "in the reference, in no __all__"
    assert public - toc == UNLISTED, "in an __all__, not in the reference"


def test_the_modules_outside_the_promise_are_in_no_public_namespace():
    for name in OUTSIDE:
        names = set(importlib.import_module(name).__all__)
        for public in map(importlib.import_module, PUBLIC):
            assert not names & set(vars(public)), (name, public.__name__)


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


MACHINERY = {
    "batched",
    "capped_by",
    "check_batch",
    "count_query",
    "ensured",
    "entry",
    "label",
    "on_state",
    "per_key",
    "plan_entry",
    "settle",
    "violating",
}
"""`TableCondition`'s machinery, which its five public subclasses inherit
without an underscore: how a condition is checked and planned, not what a
user reads. Undocumented on purpose (a page would promise them); the
underscore pass of #1288 API-5 renames them and deletes this set (ruling
180)."""

UNPROMISED = {
    # Their members are outside the promise (`docs/stability.md`).
    "sverify.engines.Native",
    "sverify.engines.Dialect",
}


def test_the_machinery_is_still_there():
    """`MACHINERY` names members `TableCondition` still has without an
    underscore; the pass that underscores them deletes the set."""
    from sverify.conditions import TableCondition

    names = set(dir(TableCondition)) | set(TableCondition.__annotations__)
    assert names >= MACHINERY


@functools.cache
def _documented_here(cls: type) -> frozenset[str]:
    """The attributes `cls` documents: a string right after an assignment
    in its body or after a `self.x = ...` in its `__init__`, or a line of
    its docstring's `Attributes:` section."""
    out: set[str] = set()
    node = ast.parse(textwrap.dedent(inspect.getsource(cls))).body[0]
    assert isinstance(node, ast.ClassDef)
    body = node.body
    inits = [f.body for f in body if isinstance(f, ast.FunctionDef) and f.name == "__init__"]
    for stmts, of_self in [(body, False), *((b, True) for b in inits)]:
        for a, b in itertools.pairwise(stmts):
            if not (isinstance(b, ast.Expr) and isinstance(b.value, ast.Constant)):
                continue
            targets = [a.target] if isinstance(a, ast.AnnAssign) else getattr(a, "targets", [])
            for t in targets:
                if of_self and isinstance(t, ast.Attribute) and ast.unparse(t.value) == "self":
                    out.add(t.attr)
                elif not of_self and isinstance(t, ast.Name):
                    out.add(t.id)
    doc = inspect.cleandoc(cls.__dict__.get("__doc__") or "")
    if section := re.search(r"^Attributes:\n((?:    .*\n?|\n)*)", doc, re.M):
        out |= set(re.findall(r"^    (\w+):", section.group(1), re.M))
    return frozenset(out)


def _undocumented(cls: type) -> list[str]:
    """`cls`'s public members, its sverify bases' included, that have no
    docstring and no line in an `Attributes:` section."""
    from sverify.conditions import TableCondition

    bases = [k for k in cls.__mro__ if _sverify(k)]
    documented = set().union(*map(_documented_here, bases))
    if issubclass(cls, TableCondition):
        documented |= MACHINERY
    seen: set[str] = set()
    missing = []
    for k in bases:
        for name in sorted(set(vars(k)) | set(vars(k).get("__annotations__", {}))):
            if name.startswith("_") or name in seen:
                continue
            seen.add(name)
            member = vars(k).get(name)
            f = _function(member)
            own_doc = getattr(member, "__doc__", None) if isinstance(member, property) else None
            own_doc = own_doc or (f.__doc__ if f else None)
            if name not in documented and not own_doc:
                missing.append(f"{k.__qualname__}.{name}")
    return missing


@needs_repo
def test_every_public_member_is_documented():
    """A member without an underscore of a public class is public
    (`docs/stability.md`), so the reference documents it: a docstring, or a
    line in its class's `Attributes:` section."""
    missing = {}
    for module in map(importlib.import_module, PUBLIC):
        for n in module.__all__:
            obj = getattr(module, n)
            name = f"{module.__name__}.{n}"
            if inspect.isclass(obj) and name not in UNPROMISED and (u := _undocumented(obj)):
                missing[name] = u
    assert missing == {}
