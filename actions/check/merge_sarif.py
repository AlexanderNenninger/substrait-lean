"""Merge SARIF logs of one tool into one log with one run: `merge_sarif.py OUT IN...`.

Code scanning takes one run per category, and the action checks each target with its own
`sverify check`. The rules are the union by id; the results are concatenated. A log that is not
JSON (a target that failed before it wrote one) is skipped, and the job's exit code says so."""

import json
import sys


def merge(logs: list[dict]) -> dict:
    out = logs[0]
    run = out["runs"][0]
    rules = {r["id"]: r for r in run["tool"]["driver"].get("rules", [])}
    results = list(run.get("results", []))
    for log in logs[1:]:
        for other in log["runs"]:
            for r in other["tool"]["driver"].get("rules", []):
                rules.setdefault(r["id"], r)
            results.extend(other.get("results", []))
    run["tool"]["driver"]["rules"] = list(rules.values())
    run["results"] = results
    out["runs"] = [run]
    return out


def main(argv: list[str]) -> int:
    logs = []
    for path in argv[2:]:
        try:
            with open(path) as f:
                logs.append(json.load(f))
        except json.JSONDecodeError:
            print(f"::warning::{path} is not SARIF", file=sys.stderr)
    if not logs:
        return 0
    with open(argv[1], "w") as f:
        json.dump(merge(logs), f, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
