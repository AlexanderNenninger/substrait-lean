"""The function table (`sverify._functions`, #544) against Lean's and itself."""

import re
from pathlib import Path

import ibis.expr.operations as ops
import pytest
import sqlglot.expressions as sge

from sverify import _functions as fns
from sverify.sql_lift import PROFILES

ROOT = Path(__file__).resolve().parents[2]
WRITE_LEAN = ROOT / "SubstraitLean" / "Write.lean"
#: The table's areas, by the name of their list in `Write.lean`.
LEAN_LISTS = {"core": "coreFns", "strings": "stringFns"}
DIALECTS = {"", "duckdb", "spark", "snowflake"}


def lean_list(name: str) -> dict[str, int]:
    """A list of `Write.lean`'s (`coreFns`, …): anchors by name."""
    text = WRITE_LEAN.read_text()
    m = re.search(rf"def {name} : List \(Nat × String\) := \[(.*?)\)\]", text, re.S)
    assert m, name
    return {n: int(a) for a, n in re.findall(r'\((\d+), "([a-z0-9_]+)"\)', m.group(1) + ")")}


@pytest.mark.parametrize("f", fns.FUNCTIONS, ids=lambda f: f.name)
def test_rows_are_lean_functions(f: fns.Fn) -> None:
    """Each row is a function of its area's list in `Write.lean`, at its anchor."""
    assert lean_list(LEAN_LISTS[f.area]).get(f.name) == f.anchor


def test_strings_complete() -> None:
    """Every string function Lean writes has a row."""
    assert {f.name for f in fns.area("strings")} == set(lean_list("stringFns"))


def test_rows_unique() -> None:
    names = [n for f in fns.FUNCTIONS for n in (f.name, *f.aliases)]
    assert len(names) == len(set(names))
    assert len({f.anchor for f in fns.FUNCTIONS}) == len(fns.FUNCTIONS)


def test_groups_and_options() -> None:
    """Every row has a group of the design, and every group's options are options."""
    for f in fns.FUNCTIONS:
        assert f.group in fns.GROUPS, f.name
        assert f.group.split(".")[0] in ("int", "fp", "str"), f.name
    for group, options in fns.GROUPS.items():
        assert set(options) <= set(fns.OPTIONS), group
    used = {o for options in fns.GROUPS.values() for o in options}
    assert used == set(fns.OPTIONS)
    for o in fns.OPTIONS.values():
        assert {b for b, _ in o.extra} <= set(o.core), o.id
        for _, fact in o.extra:
            assert (ROOT / "characterization" / "duckdb" / "facts" / f"{fact}.json").exists()


@pytest.mark.parametrize("profile", sorted(fns.CHOICES))
def test_choices(profile: str) -> None:
    """Each profile chooses, for every group and option, behaviours the core allows."""
    for (group, option), c in fns.CHOICES[profile].items():
        assert group is None or group in fns.GROUPS
        assert c.behaviours and set(c.behaviours) <= set(fns.OPTIONS[option].core), option
        assert c.default is None or set(c.default) <= set(c.behaviours), option
    for group, options in fns.GROUPS.items():
        for option in options:
            fns.choice(profile, group, option)


@pytest.mark.parametrize("group", ["fp.elem", "fp.log"])
def test_lift_profiles_agree(group: str) -> None:
    """The options the lift writes are its profile's choice: DuckDB's one
    behaviour, the reference's default."""
    for name, p in PROFILES.items():
        fixed = {"on_domain_error": p.domain_error, "on_log_zero": p.log_zero}
        for option in fns.GROUPS[group]:
            if option not in fixed:
                continue
            c = fns.choice(name, group, option)
            assert (fixed[option],) == (c.default or c.behaviours), (name, option)


def test_consumers_exist() -> None:
    """The SQL dialects, SQLGlot nodes and Ibis operations the rows name exist."""
    for f in fns.FUNCTIONS:
        assert set(f.sql) <= DIALECTS, f.name
        assert not f.expr or f.sql, f.name
        assert all(isinstance(getattr(ops, n, None), type) for n in f.ibis), f.name
        assert all(isinstance(getattr(sge, n, None), type) for n in f.lift), f.name
        assert not (f.expr or f.call) or f.op, f.name
