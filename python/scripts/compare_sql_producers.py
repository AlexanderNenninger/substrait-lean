"""Summarise a `SVERIFY_COMPARE_SQL` run (see `tests/conftest.py`): how many
of the tests' SQL strings each producer's plan verifies for, and the queries
where both verify but the rows differ. Some of those are differences between
the SQL dialects, listed in `DIALECT`: each plan means what its own SQL means.
The exit status is 1 if any other query differs, or nothing was recorded.

Usage: uv run python scripts/compare_sql_producers.py <records.jsonl>
"""

import json
import re
import sys
from collections import Counter

#: Where Calcite's SQL means something else than DataFusion's.
DIALECT = {
    r"\bpower\(": "Calcite's POWER is a DOUBLE; DataFusion's of integers an integer",
    r"\b(GREATEST|LEAST)\(": "Calcite's GREATEST/LEAST are NULL if any argument is",
    r"\bsubstr\(s, (0|-)": "Calcite's SUBSTR counts a negative start from the end",
}


def dialect(sql: str) -> str | None:
    return next((why for pat, why in DIALECT.items() if re.search(pat, sql)), None)


def main() -> int:
    records: dict[str, dict] = {}
    with open(sys.argv[1]) as f:
        for line in f:
            r = json.loads(line)
            seen = records.setdefault(r["sql"], r)
            # The same query runs on many tables: it differs if any run does.
            if r.get("same_rows") is False:
                seen["same_rows"] = False
    if not records:
        print("no SQL strings recorded")
        return 1
    pairs = Counter((r["datafusion"], r["isthmus"]) for r in records.values())
    print(f"{len(records)} distinct SQL strings")
    print("datafusion  isthmus   count")
    for (df, ist), n in pairs.most_common():
        print(f"{df:11} {ist:9} {n:5}")
    for p in ("datafusion", "isthmus"):
        n = sum(r[p] == "verified" for r in records.values())
        print(f"{p} verifies {n}")
    differ = [r["sql"] for r in records.values() if r.get("same_rows") is False]
    same = sum(r.get("same_rows") is True for r in records.values())
    print(f"both verify and run: {same} agree, {len(differ)} differ")
    unexplained = []
    for sql in differ:
        why = dialect(sql)
        print(f"  {'dialect' if why else 'DIFFERENT ROWS'}: {sql}" + (f"  ({why})" if why else ""))
        if why is None:
            unexplained.append(sql)
    return 1 if unexplained else 0


if __name__ == "__main__":
    sys.exit(main())
