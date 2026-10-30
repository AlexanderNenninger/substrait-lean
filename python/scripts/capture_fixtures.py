"""Capture real Substrait plans from DuckDB into tests/fixtures/duckdb_*.json.

The pipelines are the Ibis expressions in `sverify.examples`, compiled to SQL by
Ibis and to Substrait by DuckDB, the same route `IncrementalView.from_ibis` takes.

Run from python/:  uv run python scripts/capture_fixtures.py
"""

import json
from pathlib import Path

import ibis

from sverify.duck import connect, substrait_json
from sverify.examples import PIPELINES, UNSUPPORTED, create_tables

FIXTURES = Path(__file__).resolve().parents[2] / "tests" / "fixtures"

CAPTURED = {
    **{k: PIPELINES[k] for k in ["filter_project", "inner_join", "union_all", "self_join"]},
    # Not in the modelled fragment: recorded to pin down the rejection.
    "aggregate": UNSUPPORTED["aggregate"],
}


def main() -> None:
    con = connect()
    create_tables(con)
    for name, expr in CAPTURED.items():
        plan = json.loads(substrait_json(con, ibis.to_sql(expr, dialect="duckdb")))
        path = FIXTURES / f"duckdb_{name}.json"
        path.write_text(json.dumps(plan, indent=2) + "\n")
        print(f"wrote {path.relative_to(FIXTURES.parents[1])}")


if __name__ == "__main__":
    main()
