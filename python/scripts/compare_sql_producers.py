"""Summarise a `SVERIFY_COMPARE_SQL` run (see `tests/conftest.py`): how many
of the tests' SQL strings each producer's plan verifies for, and the queries
where both verify but the rows differ (exit status 1 if there are any, or
no records at all).

Usage: uv run python scripts/compare_sql_producers.py <records.jsonl>
"""

import json
import sys
from collections import Counter


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
    for sql in differ:
        print("  DIFFERENT ROWS:", sql)
    return 1 if differ else 0


if __name__ == "__main__":
    sys.exit(main())
