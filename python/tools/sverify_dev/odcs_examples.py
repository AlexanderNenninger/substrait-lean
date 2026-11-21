"""Read the Open Data Contract Standard's published examples (#864).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

The ODCS repository (`bitol-io/open-data-contract-standard`, Apache-2.0)
publishes example contracts for every part of the standard
(`docs/examples`). `python/tests/standards/odcs-examples-v3.2.0/` holds them
at the tag of v3.2.0, the version `sverify.odcs` writes. For each example
and each schema object in it, this module records what `sverify.odcs.read`
gives: the conditions, and each rule it does not read with the reason
(`unread`). Then it round-trips the object: a transform that passes the
object through, with its conditions as `requires` and `ensures`, is
exported with `sverify.odcs.export` and read back, and the conditions are
compared. A key stands for its uniqueness and its columns' NOT NULL, which
the export writes as `required`, so keys are compared expanded. The
outcome is `same`, the conditions that differ, or why the transform is
refused.

`python -m sverify_dev.odcs_examples` prints the totals; `--write` rewrites
the ledger `python/tests/odcs_examples.json`; `tests/test_odcs.py` compares
a fresh read with it.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import warnings
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
EXAMPLES = ROOT / "python" / "tests" / "standards" / "odcs-examples-v3.2.0"
LEDGER = ROOT / "python" / "tests" / "odcs_examples.json"


#: What each kind of unread rule, or refused round trip, waits on: an issue
#: that would read it, or why sverify does not by design.
WAITS_ON: tuple[tuple[str, dict[str, Any]], ...] = (
    ("a relationship that is not a foreign key", {"design": "sverify reads foreign keys"}),
    (
        "no single column the contract defines",
        {"design": "it names nothing, or two columns, for sverify to check"},
    ),
    ("a foreign key from another table", {"design": "it constrains the table it starts from"}),
    ("a composite foreign key", {"issue": 2223}),
    ("is not supported; cast the column", {"issue": 1958}),
    ("sverify reads no binary values", {"issue": 1958}),
    ("logicalTypeOptions.format", {"design": "a format for text, which no row breaks"}),
    ("a SQL rule of another shape", {"design": "a template the contract's runner fills in"}),
    ("a rule for engine", {"design": "another tool's own rule language"}),
    ("a share of rows", {"design": "sverify reads rules on every row"}),
    ("a lower bound on the row count", {"design": "a lower bound depends on the data"}),
    ("with a time zone on a timestamp without one", {"design": "the offset has no meaning there"}),
    (
        "without a time zone on a timestamp with one",
        {"design": "its instant depends on the session"},
    ),
)


def waits_on(reason: str) -> dict[str, Any]:
    return next((dict(w) for match, w in WAITS_ON if match in reason), {})


def _expanded(conds: list[Any]) -> list[str]:
    """Condition labels with a key as its uniqueness and NOT NULLs, and the
    two spellings of NOT NULL as one."""
    from sverify.conditions import Key, label

    out = set()
    for c in conds:
        if isinstance(c, Key):
            out.add(f"unique{c.cols}")
            out.update(f'"{col}" IS NOT NULL' for col in c.cols)
        else:
            out.add(re.sub(r'^NOT ("[^"]+") IS NULL$', r"\1 IS NOT NULL", label(c)))
    return sorted(out)


def round_trip(contract: Any, table: str) -> Any:
    """`same`, the conditions an export and a read back lose or add, or why
    the pass-through transform is refused."""
    import sverify as sv
    from sverify import odcs
    from sverify.conditions import References
    from sverify.io import StaticSource

    conds = contract.conditions(table)
    if any(isinstance(c, References) for c in conds):
        # The pass-through transform has one input; a foreign key needs the
        # object it references as a second.
        return {"not tried": "a foreign key: the round trip reads one object"}
    try:
        src = StaticSource(contract.schema(table).to_pyarrow().empty_table(), name=table)

        @sv.transform(requires={"x": conds}, ensures=conds)
        def passed(x: Any) -> Any:
            return x

        back = odcs.read(odcs.export(src.pipe(passed))).conditions()
    except Exception as e:  # noqa: BLE001 - a refusal is part of the record
        reason = _first_line(e)
        return {"refused": reason, **waits_on(reason)}
    a, b = _expanded(conds), _expanded(back)
    if a == b:
        return "same"
    return {"lost": sorted(set(a) - set(b)), "added": sorted(set(b) - set(a))}


def _first_line(e: BaseException) -> str:
    text = str(e).strip().splitlines() or [type(e).__name__]
    lines = [text[0], *(line.strip() for line in text[1:2])]
    return f"{type(e).__name__}: {' '.join(lines)}"[:300]


def entry(path: Path) -> dict[str, Any]:
    """What `read` gives for one example, per schema object."""
    from sverify import odcs
    from sverify.conditions import label

    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        try:
            contract = odcs.read(path)
        except ValueError as e:
            return {"refused": _first_line(e)}
        objects: dict[str, Any] = {}
        for table, conds in contract.tables.items():
            objects[table] = {
                "conditions": [label(c) for c in conds],
                "unread": [
                    {"column": u.column, "reason": u.reason, **waits_on(u.reason)}
                    for u in contract.unread
                    if u.table == table
                ],
                "round_trip": round_trip(contract, table) if conds else "no conditions",
            }
    return {"objects": objects}


def ledger() -> dict[str, Any]:
    results = {
        str(p.relative_to(EXAMPLES)): entry(p) for p in sorted(EXAMPLES.rglob("*.odcs.yaml"))
    }
    counts: collections.Counter[str] = collections.Counter()
    for r in results.values():
        if "refused" in r:
            counts["examples refused"] += 1
            continue
        counts["examples read"] += 1
        for o in r["objects"].values():
            counts["conditions"] += len(o["conditions"])
            counts["unread"] += len(o["unread"])
            rt = o["round_trip"]
            key = rt if isinstance(rt, str) else next(iter(rt))
            counts[f"round trip {key}"] += 1
    return {
        "source": "https://github.com/bitol-io/open-data-contract-standard/tree/v3.2.0/docs/examples",
        "license": "Apache-2.0",
        "summary": dict(sorted(counts.items())),
        "results": results,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--write", action="store_true", help="rewrite the ledger")
    args = ap.parse_args(argv)
    fresh = ledger()
    print(json.dumps(fresh["summary"], indent=1))
    if args.write:
        LEDGER.write_text(json.dumps(fresh, indent=2, ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
