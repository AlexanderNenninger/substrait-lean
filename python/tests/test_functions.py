"""The function table (`sverify._functions`, #544) against Lean's and itself."""

import functools
import json
import subprocess
from pathlib import Path

import ibis.expr.operations as ops
import pytest
import sqlglot.expressions as sge

from sverify import _functions as fns
from sverify.engine import checker_path
from sverify.sql_lift import PROFILES

ROOT = Path(__file__).resolve().parents[2]
DIALECTS = {"", "duckdb", "spark", "snowflake"}


@functools.cache
def lean_rows() -> tuple[dict, ...]:
    """Lean's function tables (`SubstraitLean/Functions.lean`), as
    `substrait-check --functions` prints them: a row per constructor."""
    out = subprocess.run(
        [str(checker_path()), "--functions"], capture_output=True, text=True, check=True
    )
    return tuple(json.loads(out.stdout))


@functools.cache
def lean_options() -> dict:
    """Lean's options table, the groups' options and the reference's choices
    (`SubstraitLean/Options.lean`), as `substrait-check --options` prints them."""
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    )
    return json.loads(out.stdout)


def lean_choice(profile: str, group: str, option: str) -> fns.Choice:
    """`ProfileTable.choice?`: the group's own row, else the option's."""
    rows = lean_options()["choices"][profile]
    found = [r for r in rows if r["group"] == group and r["option"] == option] or [
        r for r in rows if r["group"] is None and r["option"] == option
    ]
    assert found, (profile, group, option)
    c = found[0]["choice"]
    assert c["kind"] in ("oneOf", "asked"), c
    return fns.Choice(tuple(c["behaviours"]), tuple(c["default"]) if "default" in c else None)


@pytest.mark.parametrize("f", fns.FUNCTIONS, ids=lambda f: f.name)
def test_rows_are_lean_functions(f: fns.Fn) -> None:
    """Each row is Lean's: its area, anchor, group and the group's options,
    for every type Lean models the function at."""
    rows = [r for r in lean_rows() if r["name"] == f.name]
    assert rows, f.name
    for r in rows:
        assert (r["area"], r["anchor"], r["group"]) == (f.area, f.anchor, f.group)
        assert tuple(r["options"]) == f.options


def test_options_are_lean() -> None:
    """Each option is Lean's row (D1), and each group has Lean's options."""
    lean = {o["id"]: o for o in lean_options()["options"]}
    for o in fns.OPTIONS.values():
        row = lean[o.id]
        assert (row["substrait"], tuple(row["core"])) == (o.substrait, o.core), o.id
        assert tuple(tuple(e) for e in row["extra"]) == o.extra, o.id
    for group, options in fns.GROUPS.items():
        assert tuple(lean_options()["groups"][group]) == options, group


@pytest.mark.parametrize("f", fns.FUNCTIONS, ids=lambda f: f.name)
def test_reference_is_lean(f: fns.Fn) -> None:
    """The reference's choice at each of a row's options is Lean's
    (`Profile.reference.table`)."""
    for option, c in f.reference.items():
        assert c == lean_choice("reference", f.group, option), (f.name, option)


def test_tools_and_observations() -> None:
    """The tool table (D9) has one row per option, a raise with its
    precondition; the reference refines itself exactly at every option (D15)."""
    tables = lean_options()
    options = [o["id"] for o in tables["options"]]
    tools = tables["tools"]
    assert [t["option"] for t in tools] == options
    assert all((t["tool"] == "raise") == bool(t["precondition"]) for t in tools)
    assert {t["tool"] for t in tools} == {"raise", "choose", "leave_open"}
    ref = tables["observations"]["reference"]
    assert [r["option"] for r in ref] == options
    assert all(r["row"]["class"] == "refines" and r["row"]["shim"] is None for r in ref)


def test_lean_facts_exist() -> None:
    """Every fact Lean's options table cites is a document of `characterization/`."""
    facts = {fact for o in lean_options()["options"] for _, fact in o["extra"]}
    assert facts
    for fact in facts:
        engine = fact.split("-")[0]
        assert (ROOT / "characterization" / engine / "facts" / f"{fact}.json").exists(), fact


def test_strings_complete() -> None:
    """Every string function Lean writes has a row."""
    lean = {r["name"] for r in lean_rows() if r["area"] == "strings"}
    assert {f.name for f in fns.area("strings")} == lean


def test_groups_complete() -> None:
    """Every function Lean models in the table's groups alone has a row
    (`power` is also `int.arith`)."""
    groups: dict[str, set[str]] = {}
    for r in lean_rows():
        groups.setdefault(r["name"], set()).add(r["group"])
    lean = {name for name, gs in groups.items() if gs <= set(fns.GROUPS)}
    assert {f.name for f in fns.FUNCTIONS} == lean


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
