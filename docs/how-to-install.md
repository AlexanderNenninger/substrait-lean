# Install

The short form is in [the README](../python/README.md#install). The extras, the wheels and the nightly builds:

The core verifies without an engine and writes DuckDB and Snowflake SQL; `sverify[spark]` adds Spark SQL (`report.to_sql("spark")` raises `unknown dialect` without it). Extras:
`polars`, `spark` (needs Java 17 or 21), `delta`, `iceberg`,
`flight`, `testing`, `odcs`, `openlineage`, or `all`.
The `polars` and `spark` extras install the engine packages `sverify-polars`
and `sverify-spark` with their runtimes; either package alone
(`pip install sverify-spark`) verifies under its engine's semantics and
writes its SQL without the runtime. Sverify finds every installed engine
through its plugin (`sverify.profiles.ProfilePlugin`, the entry-point group
`sverify.profiles`). Wheels bundle the checker as a small native binary for Linux (x86_64,
aarch64) and macOS (arm64), Python 3.12 and later. Elsewhere (Windows, an Intel Mac) the
sdist's build stops with a message; use WSL2 or a Linux container, or set
`SVERIFY_BUILD_FROM_SOURCE=1` to build from source, which needs
[elan](https://github.com/leanprover/elan) and starts a full `lake build` of every generated Lean module,
minutes of work that can load every core.
Contributors with a built checker set `SVERIFY_PREBUILT_CHECKER=<path to substrait-check>`, and an editable install links it instead.

## Nightly builds

Each night, when `main` has changed, the
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly) gets its wheels, versioned
`<next minor>.dev<commits>+g<sha>`, so they sort after the latest release. They are not on PyPI:

```bash
# skip: installs software on the reader's machine
uv add "sverify>=0.8.0.dev0" --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly
pip install --pre sverify --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly
```

uv keeps the version and drops the page, so add it to your `pyproject.toml`;
`uv lock --upgrade-package sverify` then moves to the latest nightly:

```toml
[tool.uv]
find-links = ["https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly"]
```

Each build's wheels stay on the release for 30 days, so a wheel's own URL pins
one build for that long. `--find-links` sees every build on the page and picks
the newest. Copy a URL from the release page:

```bash
# skip: installs software on the reader's machine
pip install "sverify @ https://github.com/AlexanderNenninger/substrait-lean/releases/download/nightly/sverify-<version>-py3-none-<platform>.whl"
```
