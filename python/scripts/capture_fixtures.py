"""Capture real Substrait plans from DuckDB into tests/fixtures/duckdb_*.json.

Run from python/:  uv run python scripts/capture_fixtures.py
"""

import json
from pathlib import Path

from sverify.duck import connect, substrait_json

FIXTURES = Path(__file__).resolve().parents[2] / "tests" / "fixtures"

QUERIES = {
    "filter_project": "select id, amount * 2 as doubled from orders where amount > 10",
    "inner_join": "select o.id, c.city from orders o join customers c on o.customer = c.name",
    "union_all": "select id from orders union all select id from orders where amount < 3",
    # Not in the modelled fragment: recorded to pin down the rejection.
    "aggregate": "select customer, sum(amount) as s from orders group by customer",
}


def main() -> None:
    con = connect()
    con.sql("create table orders(id bigint, customer varchar, amount bigint)")
    con.sql("create table customers(name varchar, city varchar)")
    for name, sql in QUERIES.items():
        plan = json.loads(substrait_json(con, sql))
        path = FIXTURES / f"duckdb_{name}.json"
        path.write_text(json.dumps(plan, indent=2) + "\n")
        print(f"wrote {path.relative_to(FIXTURES.parents[1])}")


if __name__ == "__main__":
    main()
