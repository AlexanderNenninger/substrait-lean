"""The decision ledger (`decisions/*.json`) is well-formed: each file follows
`decision.schema.json` and is named by its id, every link resolves and agrees
both ways, and every section of `docs/decisions.md` has its entry."""

import json

import pytest

# A dev dependency: the installed wheel's tests go without it.
pytest.importorskip("jsonschema")

from sverify_dev import decisions  # noqa: E402

pytestmark = pytest.mark.skipif(
    not decisions.SCHEMA.is_file(), reason="decisions/ of the repository is not here"
)


def test_the_ledger_is_well_formed():
    docs = decisions.load()
    assert len(docs) >= 70
    assert decisions.validate(docs) == []


def test_the_page_renders():
    page = decisions.render(decisions.load())
    assert "## What's in force" in page


def _entry(ident, **fields):
    return {
        "id": ident,
        "date": "2026-11-20",
        "decided_by": "fable",
        "scope": "api",
        "status": "in-force",
        "summary": "s",
        **fields,
    }


def _check(tmp_path, *entries):
    for e in entries:
        (tmp_path / f"{e['id']}.json").write_text(json.dumps(e))
    return decisions.validate(decisions.load(tmp_path), headings={})


def test_a_link_agrees_both_ways(tmp_path):
    assert _check(tmp_path, _entry("F2", supersedes=["F1"]), _entry("F1")) == [
        "F2: supersedes F1, but F1 lacks superseded_by F2",
    ]


def test_a_superseded_entry_is_not_in_force(tmp_path):
    assert _check(
        tmp_path,
        _entry("F2", supersedes=["F1"]),
        _entry("F1", superseded_by=["F2"]),
        _entry("F3", status="unclear"),
        _entry("F4", amends=["F9"]),
    ) == [
        "F1: superseded by F2, but in-force",
        "F3: unclear, and no note says why",
        "F4: amends F9, which has no entry",
    ]


def test_a_file_is_named_by_its_id(tmp_path):
    (tmp_path / "F5.json").write_text(json.dumps(_entry("F6")))
    assert decisions.validate(decisions.load(tmp_path), headings={}) == [
        "F5.json: its id is F6, so the file is F6.json"
    ]


def test_the_public_ledger_stands_without_the_held_back_entries():
    # CI has no `decisions/private/`: the public entries pass on their own.
    assert decisions.validate(decisions.public(decisions.load())) == []


def test_a_held_back_entry_links_one_way(tmp_path):
    (tmp_path / "private").mkdir()
    # The held-back entry amends F1, and F1 does not name it back.
    (tmp_path / "F1.json").write_text(json.dumps(_entry("F1")))
    (tmp_path / "private" / "U-2026-11-20-a.json").write_text(
        json.dumps(_entry("U-2026-11-20-a", decided_by="user", amends=["F1"]))
    )
    (tmp_path / "F2.json").write_text(json.dumps(_entry("F2", amends=["U-2026-11-20-a"])))
    assert decisions.validate(decisions.load(tmp_path), headings={}) == [
        "F2: amends U-2026-11-20-a, which is held back",
    ]
