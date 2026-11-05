# sverify for VS Code (prototype)

The extension brings sverify's checks into the editor. When you save a
Python file that imports `sverify`, it runs the file's `@sv.transform`s and
`sv.verify` calls and shows what Lean proved where the code is written:

- Diagnostics on the expression or condition they are about: "not proved",
  "needs", "may fail", "assumes", rows that may tie, a column or table a
  contract names that does not exist.
- Quick fixes from inference: state an inferred precondition in
  `requires=`, filter the input first, guard a division with a CASE
  (`ibis.ifelse` in Ibis, `CASE WHEN` in SQL), add the key or row cap a
  route suggests, or add every suggested precondition at once. Each opens
  in the refactor preview first.
- Hovers: on a transform, its contract with each condition's status, what
  Lean knows about each output column, and the route and class per engine
  (exact, observed, shim, refused); on an output column, its proved range
  and NULL-ness and the conditions that read it.
- A code lens above each transform with the verdict, the classes on DuckDB
  and Polars and the time the check took; it opens the full report.
- Contract authoring: inside `requires`/`ensures`, completion of the
  table's columns after `_.` and in `sv.unique("…")`, and of the contract
  helpers after `sv.` (only those that belong in that list); unknown
  columns are flagged as you type, with the closest name as a fix.

[UX-NOTES.md](UX-NOTES.md) records what worked, what was awkward, and the
API changes the prototype suggests.

## How it works

The TypeScript client starts one Python process per workspace folder,
`python -m sverify_vscode serve` ([python/sverify_vscode](python/sverify_vscode)),
which imports sverify and Ibis once and answers one JSON request per check.
A check runs the file as a module named `__sverify_check__`, so code under
`if __name__ == "__main__":` (runs on data) stays out of it. Then it checks
each `sv.ContractedTransform` of the module with
`ContractedTransform.check` on the module's unbound tables
(`ibis.table(schema, name=...)`) named like its parameters, or reads its
`last_report`, and reads each `sv.Report` the module assigned to a name,
matched with the `sv.verify(...)` call assigned to it. The setting
`sverify.counterexamples` reaches the file's own calls through
`SVERIFY_COUNTEREXAMPLES`. The checker uses only sverify's public API;
[UX-NOTES.md](UX-NOTES.md#public-api-gaps) lists what that took.

The Python side places each finding in the source with the AST
(`Issue.shown`, such as `total // qty`, matched against the transform's
body and the helpers it calls, and against SQL strings), computes each fix
as text edits, and returns diagnostics, hovers, code lenses and the
contract sites completion reads. The same JSON comes from the command line:

```bash
PYTHONPATH=vscode/python python/.venv/bin/python -m sverify_vscode check vscode/demo/orders.py
```

## Try it

You need Node 20 or later and a Python environment with sverify (the
repository's `python/.venv`, after `uv sync` and `poe build`).

```bash
cd vscode && npm install && npm run compile
```

```bash
code --extensionDevelopmentPath="$PWD" demo
```

The demo workspace ([demo](demo)) holds the tour's examples:
[orders.py](demo/orders.py) (notebook 4, one finding per transform),
[payments.py](demo/payments.py) (notebook 1, proved),
[sensors.py](demo/sensors.py) (notebook 2, ties in a window) and
[mart.py](demo/mart.py) (notebook 3, a left join and the SQL model). Its
`.vscode/settings.json` points `sverify.pythonPath` at the repository's
`python/.venv`.

Settings: `sverify.pythonPath` (default: the workspace's `.venv`, then
`python3`), `sverify.checkOnSave`, `sverify.counterexamples` (inputs tried
per unproved postcondition; sverify's default is 200) and
`sverify.previewFixes`. Commands: "sverify: Check this file", "Show the
report" and "Restart the checker". The checker's log is in the "sverify"
output channel.

## Tests

```bash
cd vscode && PYTHONPATH=python ../python/.venv/bin/python -m pytest python/tests
```

```bash
cd vscode && npm test
```

```bash
cd vscode && npm run test:vscode
```

The first runs the checker on the demo files and applies every quick fix;
the second drives the checker process from Node; the third opens the demo
in a VS Code extension host and reads diagnostics, quick fixes, hovers,
code lenses and completion through VS Code's own commands.

## Limits

- Marimo notebooks (the tour itself) are not checked: their cells run only
  under `app.run()`.
- A transform is checked only on unbound tables the file defines, or where
  the file calls it; an `sv.verify` report only where the file assigns it
  to a name. A module-level call that raises stops the check at that line.
- Findings are placed by matching text: an expression written twice gets
  the first place, and a SQL issue that names no columns (`$3`) sits on the
  `sv.verify` call.
- Ranges shift with edits until the next save; hovers and fixes are from
  the last check.
