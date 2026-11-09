"""`docs/trusted-base.md` lists every construct the Lean kernel does not check
(#1088): each `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe def`,
`sorry` and `native_decide` in the Lean sources has a row, each row's names
exist, and each kernel-checked theorem is one `SubstraitLean/Examples.lean`
prints the axioms of. CI's `lean` job checks the axioms column itself
(`sverify_dev.trusted_base --check`)."""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from _repo import needs_repo

ROOT = Path(__file__).resolve().parents[2]
PAGE = ROOT / "docs" / "trusted-base.md"

pytestmark = needs_repo

#: The Lean sources of the checker and the core (`float-bounds/` is a project
#: of its own, with Mathlib, and proves what it trusts in `NativeLink`).
SOURCES = ["SubstraitLean.lean", "SubstraitCheck.lean", "Main.lean", "SubstraitLean", "core"]
#: A declaration the kernel takes on trust, and its name.
DECLARED = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
    r"(axiom|opaque|unsafe def)\s+([^\s({:]+)",
    re.M,
)
#: The constructs that need a row wherever they appear in code: `sorry` as a
#: term or a tactic (not in a message that names it).
INLINE = re.compile(
    r"@\[extern|\bnative_decide\b|(?:\bby|:=|\bexact|^|·)[ \t]*sorry\b|implemented_by", re.M
)
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def _lean_files() -> list[Path]:
    out: list[Path] = []
    for s in SOURCES:
        p = ROOT / s
        out += sorted(p.rglob("*.lean")) if p.is_dir() else [p]
    return [p for p in out if ".lake" not in p.parts]


def _code(text: str) -> str:
    """`text` without comments and docstrings."""
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m[0].count("\n"), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def _table(heading: str) -> list[list[str]]:
    """The rows of the first table under `heading`, as cells."""
    text = PAGE.read_text()
    section = text.split(f"\n## {heading}\n", 1)[1].split("\n## ", 1)[0]
    rows = [line for line in section.splitlines() if line.startswith("| ")]
    return [[c.strip() for c in r.strip("|").split(" | ")] for r in rows[1:]]


def _names(cell: str) -> set[str]:
    return set(re.findall(r"`([^`]+)`", cell))


def _trusted() -> list[tuple[str, set[str], str]]:
    """The trusted table: each row's construct, names and file cell."""
    return [(r[0], _names(r[1]), r[2]) for r in _table("Trusted")]


def _found() -> list[tuple[str, str, str]]:
    """Each construct in the Lean sources: its file, kind and name; none
    outside the repository, where `needs_repo` skips the tests."""
    if not (ROOT / "lakefile.lean").is_file():
        return []
    out = []
    for f in _lean_files():
        code = _code(f.read_text())
        rel = f.relative_to(ROOT).as_posix()
        out += [(rel, kind, name) for kind, name in DECLARED.findall(code)]
        for m in INLINE.finditer(code):
            if m[0] == "implemented_by":
                continue  # its opaque constant is declared, and listed by name
            out.append((rel, m[0].lstrip("@[").split()[-1], ""))
    return out


@pytest.mark.parametrize(("file", "kind", "name"), _found(), ids=lambda x: str(x))
def test_every_construct_has_a_row(file: str, kind: str, name: str) -> None:
    rows = [(c, ns) for c, ns, f in _trusted() if f"`{file}`" in f]
    assert rows, f"{file} has a {kind} {name} and no row in docs/trusted-base.md's trusted table"
    if name:
        assert any(name in ns for _, ns in rows), (
            f"{kind} {name} ({file}) is not in docs/trusted-base.md's trusted table"
        )
    else:
        assert any(kind in c for c, _ in rows), (
            f"{kind} in {file} has no row in docs/trusted-base.md's trusted table"
        )


def test_every_row_names_what_exists() -> None:
    """A row of a Lean construct names declarations its file has."""
    found = {(f, n) for f, _, n in _found() if n}
    for construct, names, files in _trusted():
        if not re.match(r"(axiom|opaque)", construct):
            continue
        (file,) = _names(files)
        for n in names:
            assert (file, n) in found, f"docs/trusted-base.md lists {n} in {file}, which has none"


def test_every_file_a_row_names_exists() -> None:
    for _, _, files in _trusted():
        for f in _names(files):
            if "/" in f or f.endswith(".lean") or f == "lean-toolchain":
                assert (ROOT / f.rstrip("/").split("<")[0]).exists(), f


def test_every_kernel_checked_theorem_has_its_axioms_printed() -> None:
    """Each theorem of the kernel-checked table is one `Examples.lean` prints
    the axioms of, and each axiom beyond Lean's three is a trusted row."""
    examples = (ROOT / "SubstraitLean" / "Examples.lean").read_text()
    trusted = {n for _, ns, _ in _trusted() for n in ns}
    rows = _table("Kernel-checked")
    assert rows
    for theorem, _, _, axioms in rows:
        name = theorem.strip("`")
        assert f"#print axioms Substrait.{name}\n" in examples, name
        for a in axioms.split(", "):
            assert a in STANDARD or a.removeprefix("Substrait.") in trusted, (name, a)
