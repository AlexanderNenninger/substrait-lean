"""Docstrings and docs do not repeat what a later decision replaced (#1484).

`docs/decisions.md` keeps the retired wording as history, under its
`Amended` and `Correction` lines; everywhere else the live decision's wording
stands.
"""

from _repo import ROOT, needs_repo

RETIRED = {
    "`SUM` and `AVG` of doubles, with native floats": "D25: correctly rounded exact sums",
    "the model claims only some double": "D30: exact moments rounded once",
    "to every input and output": "D36 as corrected by D31: `canon` at identity boundaries",
    "`1.0 / -0.0 = inf`": "D39: `1.0 / -0.0 = -∞` under `IEEE`",
}


@needs_repo
def test_no_retired_phrase_outside_the_decision_record() -> None:
    files = [*ROOT.joinpath("core").rglob("*.lean"), *ROOT.joinpath("docs").glob("*.md")]
    files = [f for f in files if f.name != "decisions.md" and ".lake" not in f.parts]
    assert files
    found = [
        f"{f.relative_to(ROOT)}: {phrase!r} ({why})"
        for f in files
        for phrase, why in RETIRED.items()
        if phrase in f.read_text()
    ]
    assert not found, "\n".join(found)
