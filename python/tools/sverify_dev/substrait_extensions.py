"""Generate `sverify/_substrait_extensions.json`, the table `to_substrait`
reads (#664).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

The table holds, for every function of Substrait's extension YAMLs at the
version `Profile.substrait` reads (`substrait_cases.TAG`), each impl with its
YAML's URN, its kind (scalar, aggregate, window), its arguments' types (or
an enum argument's values), whether it is variadic, its return type
derivation and its options with their values. `sverify.substrait_export`
picks the impl for a call from the argument types, and writes the URN, the
compound name and the output type from it.

`python -m sverify_dev.substrait_extensions` checks the table against the
YAMLs (exit 1 when stale); `--write` rewrites it.
`tests/test_substrait_export.py` runs the check where the YAMLs are fetched.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import yaml

from sverify_dev.substrait_cases import TAG, fetch

TABLE = Path(__file__).resolve().parents[2] / "src" / "sverify" / "_substrait_extensions.json"

_KINDS = {
    "scalar_functions": "scalar",
    "aggregate_functions": "aggregate",
    "window_functions": "window",
}


def _arg(a: dict) -> dict:
    if "options" in a:
        return {"enum": list(a["options"])}
    return {"type": str(a["value"]).strip()}


def build(ext_dir: Path | None = None) -> dict[str, Any]:
    """The table, from the YAMLs in `ext_dir` (default: fetched at `TAG`)."""
    if ext_dir is None:
        ext_dir = fetch() / "extensions"
    functions: dict[str, list[dict]] = {}
    for path in sorted(ext_dir.glob("*.yaml")):
        doc = yaml.safe_load(path.read_text())
        urn = doc["urn"]
        for key, kind in _KINDS.items():
            for f in doc.get(key) or []:
                for impl in f.get("impls") or []:
                    row: dict[str, Any] = {
                        "urn": urn,
                        "kind": kind,
                        "args": [_arg(a) for a in impl.get("args") or []],
                        "return": str(impl["return"]).strip(),
                    }
                    if impl.get("variadic"):
                        row["variadic"] = impl["variadic"].get("min", 0)
                    if impl.get("options"):
                        row["options"] = {k: list(v["values"]) for k, v in impl["options"].items()}
                    functions.setdefault(f["name"], []).append(row)
    return {"substrait": TAG.removeprefix("v"), "functions": functions}


def render(table: dict[str, Any]) -> str:
    return json.dumps(table, indent=1, sort_keys=True) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true", help="rewrite the table")
    args = parser.parse_args(argv)
    text = render(build())
    if args.write:
        TABLE.write_text(text)
        print(f"wrote {TABLE}")
        return 0
    if not TABLE.exists() or TABLE.read_text() != text:
        print(f"{TABLE} is stale: python -m sverify_dev.substrait_extensions --write")
        return 1
    print("up to date")
    return 0


if __name__ == "__main__":
    sys.exit(main())
