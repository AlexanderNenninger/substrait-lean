"""The public API is `sverify`, `sverify.io`, `sverify.engines`,
`sverify.testing`, `sverify.errors`, `sverify.cli`, `sverify.odcs` and
`sverify.openlineage`, and every name in it is documented: a class or
function by its own docstring, any other value in its module's docstring."""

import importlib
import inspect

import pytest

from _repo import ROOT, needs_repo

PUBLIC = [
    "sverify",
    "sverify.io",
    "sverify.engines",
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


HELD = {"nodes.Group", "nodes.Refresh", "nodes.Status", "nodes.NodeStatus", "nodes.StageRefresh"}
"""Documented because users hold them (`Node.refresh()`, `status()`,
`sv.group`), and in no `__all__`."""

UNLISTED = {"engines.create_table", "engines.table_rows"}
"""In an `__all__` and out of the reference: deprecated."""


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
    assert toc - public == HELD, "in the reference, in no __all__"
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


def test_verdict_has_no_truth_value():
    """`assert report.verdict` must not pass on UNPROVED: it raises instead."""
    from sverify import Verdict

    for v in Verdict:
        with pytest.raises(TypeError):
            bool(v)
        with pytest.raises(TypeError):
            assert v
