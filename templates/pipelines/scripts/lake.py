"""What the workflows run, so that they stay a few lines each and the tests
run the same steps.

    python scripts/lake.py check   [--out check.json] [--comment comment.md]
    python scripts/lake.py refresh [--out refresh.json] [--alert alert.md] [--check check.json]
    python scripts/lake.py catalog --out site [--check check.json] [--refresh refresh.json]
                                   [--data auto|snapshot|none|link:<url>] [--stage production]
                                   [--title …] [--banner …]
    python scripts/lake.py preview --refresh refresh.json --pr <n>
    python scripts/lake.py drop

`check` runs `sverify check --json` on every pipeline file (`pipelines/*.py`
but helpers starting with `_`), prints GitHub annotations for each problem
and writes the plain-language contract as Markdown for the PR comment.
`refresh` runs `sverify refresh --json` on each node `pipelines.toml` lists
and, when one fails, writes the text of the alert issue. `catalog` writes a
static site: an index and one page per stored table with its proved facts,
description, lineage, freshness, a chart and a query box (DuckDB-WASM).
`preview` prints a pull request's preview comment, and `drop` deletes the
current stage's tables (a closed pull request's).

Each command exits with the worst exit code of the `sverify` runs: 0
proved, 1 not proved, 2 refused, 3 budget exceeded, 4 error.

Only sverify's CLI (`sverify.cli.main`, in this process), its public
`sverify.io` and delta-rs are used.
"""

from __future__ import annotations

import argparse
import contextlib
import html
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
CATALOG = ROOT / "catalog"
EXPLAIN = "`sverify explain <code>` says what a [code] means."


def config() -> dict[str, Any]:
    with (ROOT / "pipelines.toml").open("rb") as f:
        return tomllib.load(f)


def sverify(*args: str) -> tuple[int, dict[str, Any]]:
    """Run the `sverify` CLI with `--json` in this process (`sverify.cli.main`):
    its exit code and document.

    One process for every step: sverify, Ibis and DuckDB load once, and the
    checker's answers are memoized, so a refresh after a check reuses the
    check's proofs."""
    from sverify.cli import main

    out = io.StringIO()
    try:
        with contextlib.redirect_stdout(out):
            code = main([*args, "--json"])
    except SystemExit as e:  # argparse
        code = e.code if isinstance(e.code, int) else 4
    text = out.getvalue()
    # The JSON document is the last thing printed; a pipeline may print before it.
    start = text.find("{\n")
    try:
        doc = json.loads(text[start:] if start >= 0 else text)
    except json.JSONDecodeError:
        doc = {"exit": code or 4, "error": {"code": "error", "type": "CLI", "message": text}}
    return code, doc


def worst(codes: list[int]) -> int:
    return max(codes, default=0)


def lake() -> str:
    return os.environ.get("SVERIFY_LAKE", str(ROOT / "lake")).rstrip("/")


def summary(text: str) -> None:
    """Append Markdown to the job's summary page, where there is one."""
    if path := os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(path, "a") as f:
            f.write(text + "\n")


# check


def pipeline_files() -> list[str]:
    return sorted(
        str(p.relative_to(ROOT))
        for p in (ROOT / "pipelines").glob("*.py")
        if not p.name.startswith("_")
    )


def def_line(file: str, name: str) -> int:
    """The line of `def name(` in `file`, for annotations; 1 if not found."""
    pattern = re.compile(rf"^\s*def {re.escape(name)}\(")
    for i, line in enumerate((ROOT / file).read_text().splitlines(), 1):
        if pattern.match(line):
            return i
    return 1


def annotate(level: str, file: str, line: int, title: str, message: str) -> None:
    message = message.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    print(f"::{level} file={file},line={line},title={title}::{message}")


def comment(docs: list[dict[str, Any]], code: int) -> str:
    """The PR comment: the contract of every file in plain words."""
    status = {0: "proved", 1: "not proved", 2: "refused", 3: "budget exceeded", 4: "error"}
    lines = ["<!-- sverify-check -->", f"## Contract: {status.get(code, 'error')}", ""]
    for doc in docs:
        items = doc.get("items", [])
        lines.append(f"### `{doc.get('file')}`: {doc.get('status', 'error').replace('_', ' ')}")
        lines.append("")
        for item in items:
            label = item["name"]
            s = item.get("summary") or {}
            lines.append(f"**{label}** ({item['status'].replace('_', ' ')})")
            lines.append("")
            if s.get("guarantees"):
                lines.append("The output guarantees:")
                lines += [f"- {g}" for g in s["guarantees"]]
                lines.append("")
            if s.get("checks"):
                lines.append("Each refresh checks on the data:")
                lines += [f"- {c}" for c in s["checks"]]
                lines.append("")
            if item.get("problems"):
                lines.append("Not proved:")
                for p in item["problems"]:
                    extra = (
                        f" Counterexample: `{p['counterexample']}`."
                        if "counterexample" in p
                        else ""
                    )
                    lines.append(f"- {p['message']} `[{p['code']}]`{extra}")
                lines.append("")
        for t in doc.get("unchecked", []):
            lines.append(f"- {t}: the file never applies it `[unchecked]`")
        if err := doc.get("error"):
            lines.append(f"Error `[{err['code']}]`: {err['message']}")
            lines.append("")
    if code:
        lines.append(
            f"{EXPLAIN} `sverify suggest <file> --apply` adds the preconditions a proof needs."
        )
    return "\n".join(lines).rstrip() + "\n"


def cmd_check(args: argparse.Namespace) -> int:
    docs, codes = [], []
    for file in pipeline_files():
        code, doc = sverify("check", file)
        doc.setdefault("file", file)
        docs.append(doc)
        codes.append(code)
        for item in doc.get("items", []):
            line = def_line(file, item["name"])
            for p in item.get("problems", []):
                annotate("error", file, line, f"sverify [{p['code']}]", p["message"])
        if err := doc.get("error"):
            annotate("error", file, 1, f"sverify [{err['code']}]", err["message"])
    code = worst(codes)
    text = comment(docs, code)
    if args.out:
        Path(args.out).write_text(json.dumps({"exit": code, "files": docs}, indent=2))
    if args.comment:
        Path(args.comment).write_text(text)
    summary(text)
    print(text)
    return code


# refresh


def alert(runs: list[dict[str, Any]]) -> str:
    """The text of the issue a failed refresh opens."""
    run_url = ""
    if os.environ.get("GITHUB_RUN_ID"):
        server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
        run_url = f"{server}/{os.environ.get('GITHUB_REPOSITORY')}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
    lines = ["<!-- sverify-alert -->", "The scheduled refresh failed.", ""]
    for r in runs:
        if r["exit"] == 0:
            continue
        doc, err = r["result"], r["result"].get("error") or {}
        lines.append(f"### `{r['target']}`: {doc.get('status', 'error').replace('_', ' ')}")
        lines.append("")
        lines.append(
            f"`[{err.get('code', 'error')}]` {err.get('type', '')}: {err.get('message', '')}"
        )
        lines.append("")
        for item in doc.get("items", []):
            for p in item.get("problems", []):
                lines.append(f"- {item['name']}: {p['message']} `[{p['code']}]`")
        lines.append("")
    if any((r["result"].get("error") or {}).get("type") == "PreconditionError" for r in runs):
        lines += [
            "The data broke a precondition that the proof rests on, so the node stopped "
            "before it wrote. Look at the rows the message names: if the source changed "
            "for good, change the pipeline's `requires=` and its transform in a pull request.",
            "",
        ]
    lines += [
        "What to do:",
        "- exit 1 (not proved) or 2 (refused): the data or the pipeline changed. "
        "Run `sverify check` on the file, or comment `@claude fix this` here.",
        "- exit 3 (budget): raise `SVERIFY_MEMORY_LIMIT` or the timeout.",
        "- exit 4 (error): read the log of the run.",
        "",
        f"{EXPLAIN} This issue closes on the next refresh that succeeds.",
    ]
    if run_url:
        lines.append(f"\nRun: {run_url}")
    return "\n".join(lines) + "\n"


def cmd_refresh(args: argparse.Namespace) -> int:
    if args.check:
        # The check first, in this process: the refresh reuses its proofs.
        cmd_check(argparse.Namespace(out=args.check, comment=None))
    runs, codes = [], []
    for p in config().get("pipeline", []):
        for node in p.get("refresh", []):
            target = f"{p['file']}:{node}"
            code, doc = sverify("refresh", target)
            runs.append({"target": target, "exit": code, "result": doc})
            codes.append(code)
            for n in doc.get("nodes", []):
                print(n["summary"])
            if code:
                err = doc.get("error") or {}
                annotate(
                    "error", p["file"], 1, f"sverify [{err.get('code')}]", str(err.get("message"))
                )
    code = worst(codes)
    out = {"exit": code, "at": datetime.now(UTC).isoformat(timespec="seconds"), "runs": runs}
    if args.out:
        Path(args.out).write_text(json.dumps(out, indent=2))
    lines = [f"## Refresh: {'ok' if code == 0 else f'failed (exit {code})'}", ""]
    for r in runs:
        for n in r["result"].get("nodes", []):
            w = n.get("write") or {}
            lines.append(
                f"- `{n['node']}`: {n.get('started')}; "
                + (
                    f"v{w.get('version')}, +{w.get('inserted')} −{w.get('deleted')}"
                    if w
                    else "no write"
                )
            )
    summary("\n".join(lines))
    if code and args.alert:
        Path(args.alert).write_text(alert(runs))
    return code


# catalog


def tables(root: str) -> list[str]:
    """The Delta tables directly under `root`."""
    from deltalake import DeltaTable

    cfg = config().get("table", {})
    names: list[str] = []
    if "://" not in root:
        if Path(root).is_dir():
            names = sorted(p.parent.name for p in Path(root).glob("*/_delta_log"))
    else:
        names = sorted(cfg)
    return [n for n in names if DeltaTable.is_deltatable(f"{root}/{n}")]


PALETTE = [
    "#2563eb",
    "#dc2626",
    "#16a34a",
    "#9333ea",
    "#ea580c",
    "#0891b2",
    "#ca8a04",
    "#db2777",
    "#4b5563",
    "#65a30d",
    "#7c3aed",
    "#0d9488",
]


def compact(v: float) -> str:
    """1234567 as 1.2M: axis labels short enough for a phone."""
    for div, suffix in ((1e12, "T"), (1e9, "B"), (1e6, "M"), (1e3, "k")):
        if abs(v) >= div:
            return f"{v / div:.3g}{suffix}"
    return f"{v:.3g}"


def chart_svg(arrow: Any, spec: dict[str, str]) -> str:
    """A line chart of `y` over `x`, one line per `series`, as inline SVG."""
    import duckdb

    con = duckdb.connect()
    con.register("t", arrow)
    where = f"WHERE {spec['where']}" if spec.get("where") else ""
    series = spec.get("series")
    s = f"CAST({series} AS VARCHAR)" if series else "''"
    rows = con.execute(
        f"SELECT {s} AS s, CAST({spec['x']} AS VARCHAR) AS x, CAST({spec['y']} AS DOUBLE) AS y "
        f"FROM t {where} ORDER BY 1, 2"
    ).fetchall()
    rows = [r for r in rows if r[2] is not None]
    if not rows:
        return ""
    xs = sorted({r[1] for r in rows})
    names = list(dict.fromkeys(r[0] for r in rows))[: len(PALETTE)]
    lo, hi = min(0.0, min(r[2] for r in rows)), max(r[2] for r in rows)
    hi = hi if hi > lo else lo + 1
    w, h, left, bottom, top = 480, 260, 44, 26, 10
    px = lambda i: left + (w - left - 8) * (i / max(len(xs) - 1, 1))  # noqa: E731
    py = lambda v: top + (h - top - bottom) * (1 - (v - lo) / (hi - lo))  # noqa: E731
    out = [
        f'<svg viewBox="0 0 {w} {h}" role="img" aria-label="{html.escape(spec.get("label", ""))}">'
    ]
    for k in range(5):
        v = lo + (hi - lo) * k / 4
        y = py(v)
        out.append(f'<line x1="{left}" x2="{w - 8}" y1="{y:.1f}" y2="{y:.1f}" class="grid"/>')
        out.append(f'<text x="{left - 6}" y="{y + 4:.1f}" text-anchor="end">{compact(v)}</text>')
    step = max(1, len(xs) // 6)
    for i, x in enumerate(xs):
        if i % step == 0 or i == len(xs) - 1:
            out.append(
                f'<text x="{px(i):.1f}" y="{h - 8}" text-anchor="middle">{html.escape(x)}</text>'
            )
    for j, name in enumerate(names):
        pts = " ".join(f"{px(xs.index(r[1])):.1f},{py(r[2]):.1f}" for r in rows if r[0] == name)
        out.append(f'<polyline points="{pts}" fill="none" stroke="{PALETTE[j]}" stroke-width="2"/>')
    out.append("</svg>")
    legend = "".join(
        f'<span><i style="background:{PALETTE[j]}"></i>{html.escape(n)}</span>'
        for j, n in enumerate(names)
        if n
    )
    return "".join(out) + (f'<p class="legend">{legend}</p>' if legend else "")


def rows_html(arrow: Any, limit: int = 20) -> str:
    head = arrow.slice(0, limit).to_pylist()
    if not head:
        return "<p>No rows.</p>"
    cols = arrow.column_names
    th = "".join(f"<th>{html.escape(c)}</th>" for c in cols)
    body = "".join(
        "<tr>"
        + "".join(f"<td>{html.escape('' if r[c] is None else str(r[c]))}</td>" for c in cols)
        + "</tr>"
        for r in head
    )
    return f'<div class="scroll"><table><thead><tr>{th}</tr></thead><tbody>{body}</tbody></table></div>'


def page(title: str, body: str, banner: str | None, depth: str = "") -> str:
    b = f'<p class="banner">{html.escape(banner)}</p>' if banner else ""
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<link rel="stylesheet" href="{depth}style.css">
</head><body><main>{b}{body}</main></body></html>
"""


def contract_words(view: str, checks: list[dict[str, Any]]) -> dict[str, list[str]] | None:
    for doc in checks:
        for item in doc.get("items", []):
            if item["name"] == view and item.get("summary"):
                return item["summary"]
    return None


def freshness(ms: int | None) -> str:
    if not ms:
        return "unknown"
    return datetime.fromtimestamp(ms / 1000, UTC).strftime("%Y-%m-%d %H:%M UTC")


def data_mode(mode: str, stage: str | None) -> str:
    """`SVERIFY_CATALOG_DATA` overrides `mode`. `auto`: with everything in your repository, a public repository's
    pages read the `data` branch's files (raw.githubusercontent.com), a
    private one's a snapshot in the site; for enterprise, no data in the
    site (GitHub Pages may be public)."""
    mode = os.environ.get("SVERIFY_CATALOG_DATA") or mode
    if mode != "auto":
        return mode
    if (os.environ.get("SVERIFY_STORE") or "repository") != "repository":
        return "none"
    repo = os.environ.get("GITHUB_REPOSITORY")
    if repo and stage and os.environ.get("REPOSITORY_PUBLIC") == "true":
        return f"link:https://raw.githubusercontent.com/{repo}/data/{stage}"
    return "snapshot"


def cmd_preview(args: argparse.Namespace) -> int:
    """The pull request's preview comment: what the refresh wrote, and the
    link to the preview catalog."""
    doc = json.loads(Path(args.refresh).read_text())
    pages = ""
    if repo := os.environ.get("GITHUB_REPOSITORY"):
        done = subprocess.run(
            ["gh", "api", f"repos/{repo}/pages", "--jq", ".html_url"],
            capture_output=True,
            text=True,
            check=False,
        )
        pages = done.stdout.strip()
    stage = os.environ.get("STAGE", f"staging/pr-{args.pr}")
    lines = ["<!-- sverify-preview -->", "## Preview", ""]
    if doc["exit"] == 0:
        lines.append(f"The pipelines ran against the real sources into `{stage}/`.")
    else:
        lines.append(f"The preview refresh failed (exit {doc['exit']}): see the run's summary.")
    lines.append("")
    if pages:
        lines.append(
            f"Catalog: {pages.rstrip('/')}/pr/{args.pr}/ (live once the pages workflow finishes)"
        )
    else:
        lines.append(
            "Turn on GitHub Pages (Settings, Pages, Source: GitHub Actions) for a preview catalog."
        )
    lines.append("")
    for r in doc["runs"]:
        for n in r["result"].get("nodes", []):
            w = n.get("write") or {}
            lines.append(
                f"- `{n['node']}`: {w.get('inserted', 0)} rows written, {w.get('deleted', 0)} deleted"
            )
        if r["exit"]:
            e = r["result"].get("error") or {}
            lines.append(f"- `{r['target']}`: `[{e.get('code')}]` {e.get('message')}")
    print("\n".join(lines))
    return 0


def cmd_drop(args: argparse.Namespace) -> int:
    """Delete the current stage's tables (`SVERIFY_LAKE`): a closed PR's."""
    root = lake()
    if "://" not in root:
        shutil.rmtree(root, ignore_errors=True)
    else:
        import pyarrow.fs as pafs

        fs, path = pafs.FileSystem.from_uri(root)
        fs.delete_dir_contents(path, missing_dir_ok=True)
    print(f"dropped {root}")
    return 0


def cmd_catalog(args: argparse.Namespace) -> int:
    import pyarrow.parquet as pq
    from deltalake import DeltaTable
    from sverify.io import DeltaSource

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    shutil.copy(CATALOG / "style.css", out / "style.css")
    shutil.copy(CATALOG / "query.js", out / "query.js")
    cfg = config().get("table", {})
    checks = (
        json.loads(Path(args.check).read_text())["files"]
        if args.check and Path(args.check).exists()
        else []
    )
    refreshed = (
        json.loads(Path(args.refresh).read_text())
        if args.refresh and Path(args.refresh).exists()
        else None
    )
    root = lake()
    args.data = data_mode(args.data, args.stage)
    print(f"catalog: data {args.data}")
    names = tables(root)
    entries = []
    for name in names:
        uri = f"{root}/{name}"
        dt = DeltaTable(uri)
        contract = DeltaSource(uri).contract()
        arrow = dt.to_pyarrow_table()
        last = dt.history(1)[0] if dt.version() >= 0 else {}
        meta = cfg.get(name, {})
        files: list[str] = []
        if args.data == "snapshot":
            (out / "data").mkdir(exist_ok=True)
            pq.write_table(arrow, out / "data" / f"{name}.parquet")
            files = [f"data/{name}.parquet"]
        elif args.data.startswith("link:"):
            base = args.data.removeprefix("link:").rstrip("/")
            files = [
                f"{base}/{name}/{a}"
                for a in dt.get_add_actions(flatten=True).column("path").to_pylist()
            ]
        entries.append(
            {
                "name": name,
                "title": meta.get("title", name),
                "description": meta.get("description", "").strip(),
                "source": meta.get("source"),
                "source_url": meta.get("source_url"),
                "rows": arrow.num_rows,
                "version": dt.version(),
                "updated": freshness(last.get("timestamp")),
                "schema": [(f.name, str(f.type)) for f in arrow.schema],
                "contract": None if contract is None else json.loads(contract.to_json()),
                "words": contract_words(contract.view, checks) if contract else None,
                "files": files,
                "chart": chart_svg(arrow, meta["chart"]) if meta.get("chart") else "",
                "chart_label": (meta.get("chart") or {}).get("label", ""),
                "preview": rows_html(arrow) if args.data != "none" else "",
            }
        )
    for e in entries:
        (out / f"{e['name']}.html").write_text(table_page(e, names, args))
        (out / f"{e['name']}.json").write_text(
            json.dumps(
                {
                    k: e[k]
                    for k in (
                        "name",
                        "title",
                        "rows",
                        "version",
                        "updated",
                        "schema",
                        "contract",
                        "words",
                        "files",
                    )
                },
                indent=2,
            )
        )
    (out / "index.html").write_text(index_page(entries, refreshed, args))
    print(f"catalog: {len(entries)} table(s) in {out}")
    return 0


def table_page(e: dict[str, Any], names: list[str], args: argparse.Namespace) -> str:
    c = e["contract"] or {}
    facts: list[str] = []
    if e["words"]:
        facts += [html.escape(g) for g in e["words"].get("guarantees", [])]
    else:
        facts += [f"no two rows share ({html.escape(', '.join(u))})" for u in c.get("unique", [])]
        facts += [f"{html.escape(n)} is never NULL" for n in c.get("not_null", [])]
        facts += [html.escape(s) for s in c.get("checks", {}).values()]
    checks = [html.escape(x) for x in (e["words"] or {}).get("checks", [])]
    lineage = []
    for src, v in (c.get("sources") or {}).items():
        label = (
            f'<a href="{html.escape(src)}.html">{html.escape(src)}</a>'
            if src in names
            else html.escape(src)
        )
        lineage.append(f"<li>{label} at version {v}</li>")
    source = ""
    if e["source"]:
        s = html.escape(e["source"])
        source = f'<p class="muted">Source: {f"<a href={html.escape(e["source_url"])!r}>{s}</a>" if e["source_url"] else s}</p>'
    schema = "".join(
        f"<tr><td>{html.escape(n)}</td><td>{html.escape(t)}</td></tr>" for n, t in e["schema"]
    )
    query = ""
    if e["files"]:
        query = f"""
<h2>Query</h2>
<p class="muted">Runs in your browser with DuckDB-WASM, on the table's Parquet files.</p>
<textarea id="sql" rows="3" spellcheck="false">SELECT * FROM {e["name"]} LIMIT 50</textarea>
<button id="run">Run</button>
<div id="result" class="scroll"></div>
<script type="module">
import {{ attach }} from "./query.js";
attach({json.dumps(e["name"])}, {json.dumps(e["files"])});
</script>"""
    body = f"""
<p><a href="index.html">All tables</a></p>
<h1>{html.escape(e["title"])}</h1>
<p class="muted"><code>{html.escape(e["name"])}</code> · {e["rows"]:,} rows · version {e["version"]} · updated {e["updated"]}</p>
{"".join(f"<p>{html.escape(p)}</p>" for p in e["description"].split(chr(10) + chr(10)) if p.strip())}
{source}
{f"<h2>{html.escape(e["chart_label"] or "Chart")}</h2><figure>{e["chart"]}</figure>" if e["chart"] else ""}
<h2>Proved about every row</h2>
<ul>{"".join(f"<li>{f}</li>" for f in facts) or "<li>Nothing recorded.</li>"}</ul>
{f"<h2>Checked on the data at each refresh</h2><ul>{"".join(f"<li>{x}</li>" for x in checks)}</ul>" if checks else ""}
<h2>Lineage</h2>
<ul>{"".join(lineage) or "<li>No sources recorded.</li>"}</ul>
<h2>Columns</h2>
<div class="scroll"><table><thead><tr><th>column</th><th>type</th></tr></thead><tbody>{schema}</tbody></table></div>
{f"<h2>First rows</h2>{e['preview']}" if e["preview"] else ""}
{query}
<p class="muted">Plan <code>{html.escape(str(c.get("plan", ""))[:12])}</code>, contract record format {c.get("format", "?")}.</p>
"""
    return page(e["title"], body, args.banner)


def index_page(
    entries: list[dict[str, Any]], refreshed: dict[str, Any] | None, args: argparse.Namespace
) -> str:
    rows = "".join(
        f'<li><a href="{html.escape(e["name"])}.html">{html.escape(e["title"])}</a>'
        f'<span class="muted"> · {e["rows"]:,} rows · updated {e["updated"]}</span></li>'
        for e in entries
    )
    status = ""
    if refreshed is not None:
        ok = refreshed.get("exit") == 0
        status = f'<p class="{"ok" if ok else "bad"}">Last refresh {html.escape(refreshed.get("at", ""))}: {"ok" if ok else "failed"}</p>'
    body = f"""<h1>{html.escape(args.title)}</h1>{status}
<ul class="tables">{rows or "<li>No tables yet: run the refresh workflow.</li>"}</ul>
<p class="muted">Built by sverify at {datetime.now(UTC).strftime("%Y-%m-%d %H:%M UTC")}.</p>"""
    return page(args.title, body, args.banner)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="lake.py", description=__doc__.split("\n\n")[0])
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("check")
    c.add_argument("--out")
    c.add_argument("--comment")
    c.set_defaults(run=cmd_check)
    r = sub.add_parser("refresh")
    r.add_argument("--out")
    r.add_argument("--alert")
    r.add_argument("--check", help="run check first and write its document here")
    r.set_defaults(run=cmd_refresh)
    g = sub.add_parser("catalog")
    g.add_argument("--out", required=True)
    g.add_argument("--check")
    g.add_argument("--refresh")
    g.add_argument(
        "--data", default="auto", help="auto, snapshot, none or link:<base url of the lake>"
    )
    g.add_argument("--stage", help="the stage's folder on the data branch, for --data auto")
    g.add_argument("--title", default="Data catalog")
    g.add_argument("--banner")
    g.set_defaults(run=cmd_catalog)
    v = sub.add_parser("preview")
    v.add_argument("--refresh", required=True)
    v.add_argument("--pr", required=True)
    v.set_defaults(run=cmd_preview)
    d = sub.add_parser("drop")
    d.set_defaults(run=cmd_drop)
    args = p.parse_args(argv)
    os.chdir(ROOT)  # the pipelines' paths are relative to the repository
    return args.run(args)


if __name__ == "__main__":
    sys.exit(main())
