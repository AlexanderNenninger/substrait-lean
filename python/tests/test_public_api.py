"""The public API (`docs/stability.md`) is the `__all__` of `sverify`,
`sverify.io`, `sverify.engines`, `sverify.types`, `sverify.testing`,
`sverify.errors`, `sverify.cli`, `sverify.odcs` and `sverify.openlineage`,
and the members without an underscore of the classes among them. Every name
in it is documented (a class or function by its own docstring, any other
value in its module's docstring), the API reference lists each, and every
sverify class a public name returns, holds or takes is public too."""

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


def _hints(obj, owner) -> dict:
    """The resolved type hints of `obj`, where the names its module imports
    for type checking only are looked up among sverify's modules."""
    names: dict = {k: getattr(typing, k) for k in typing.__all__}
    for mod in list(sys.modules.values()):
        if getattr(mod, "__name__", "").startswith("sverify"):
            for k, v in vars(mod).items():
                names.setdefault(k, v)
    module = sys.modules[obj.__module__]
    local = dict(vars(owner)) if inspect.isclass(owner) else None
    try:
        return typing.get_type_hints(obj, globalns={**names, **vars(module)}, localns=local)
    except (NameError, AttributeError):  # a third-party type (polars, duckdb, hypothesis)
        return {}


def _reached(obj):
    """The hints of a public function, or of a class's public fields and of
    its public methods' and properties' parameters and returns."""
    if inspect.isclass(obj):
        yield from (t for n, t in _hints(obj, obj).items() if not n.startswith("_"))
        for n, member in vars(obj).items():
            f = member.fget if isinstance(member, property) else getattr(member, "__func__", member)
            if not n.startswith("_") and inspect.isfunction(f):
                yield from _hints(f, obj).values()
    elif inspect.isfunction(obj):
        yield from _hints(obj, obj).values()


def _classes(hint):
    if inspect.isclass(hint):
        yield hint
    for arg in typing.get_args(hint):
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
    while todo:
        obj = todo.pop()
        if id(obj) in seen:
            continue
        seen.add(id(obj))
        for hint in _reached(obj):
            for cls in _classes(hint):
                if cls.__module__.partition(".")[0] != "sverify":
                    continue
                name = f"{cls.__module__}.{cls.__qualname__}"
                if id(cls) not in public and name not in EXCLUDED:
                    missing[name] = obj.__qualname__
                todo.append(cls)
    assert missing == {}, "reached, and in no public __all__ (name: reached from)"


def test_verdict_has_no_truth_value():
    """`assert report.verdict` must not pass on UNPROVED: it raises instead."""
    from sverify import Verdict

    for v in Verdict:
        with pytest.raises(TypeError):
            bool(v)
        with pytest.raises(TypeError):
            assert v
