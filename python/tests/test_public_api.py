"""The public API is `sverify`, `sverify.io`, `sverify.engines` and
`sverify.errors`, and every name in it is documented: a class or function by
its own docstring, any other value in its module's docstring."""

import importlib
import inspect

import pytest

PUBLIC = ["sverify", "sverify.io", "sverify.engines", "sverify.errors"]


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
        "Changes",
        "Node",
        "Report",
        "asof_join",
        "connect",
        "group",
        "references",
        "sql",
        "transform",
        "unique",
        "verify",
    ]
