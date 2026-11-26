#!/usr/bin/env bash
# Run the tests as the Wheels workflow does: from a copy of python/tests and
# python/tools outside the repository, against an install with the wheel's
# runtime extras (`all`) and the test
# dependencies listed here, nothing else. Tests
# that read repository files must carry `needs_repo` (tests/_repo.py); a
# test that imports a package missing below fails here.
#
#   wheel_tests.sh --wheel <path.whl> [--engine-wheel <path.whl>]... [--fast] [--python <version>] [pytest args...]
#   wheel_tests.sh --editable <python dir> [--fast] [--python <version>] [pytest args...]
#
# The engine packages (`engines/<engine>/`, #1189) install beside sverify:
# from their built wheels (`--engine-wheel`, one per package), or editable
# from the checkout with `--editable`. Their tests run with sverify's.
#
# `--fast` runs `poe test`'s set: no `slow` tests, the `dev` Hypothesis
# profile. Used by `.github/workflows/wheels.yml` (the built wheel) and by
# `outside-repo` in `.github/workflows/ci.yml` (an editable install, on every
# pull request that changes python/), so the two can't drift apart.
set -euo pipefail

# The absolute path of a file, as uv reads it: Git Bash on Windows writes
# `/d/a/x`, which a `file://` URL keeps as it is, so take Windows' form there.
abs() {
  local dir
  dir=$(cd "$(dirname "$1")" && { pwd -W 2>/dev/null || pwd; })
  echo "$dir/$(basename "$1")"
}
# `file:///D:/a/x.whl` on Windows, `file:///a/x.whl` elsewhere.
uri() { local p; p=$(abs "$1"); echo "file:///${p#/}"; }

here=$(cd "$(dirname "$0")/.." && pwd)
#: The engine packages whose tests run here (`python/pyproject.toml`'s `testpaths`).
engines=(polars spark duckdb)
install=() python=() select=()
while [ $# -gt 0 ]; do
  case "$1" in
    --wheel) install+=(--with "sverify[all] @ $(uri "$2")"); shift 2 ;;
    --engine-wheel) install+=(--with "$(abs "$2")"); shift 2 ;;
    --editable)
      install+=(--with-editable "$(cd "$2" && pwd)[all]")
      for e in "${engines[@]}"; do install+=(--with-editable "$here/../engines/$e"); done
      shift 2 ;;
    --fast) export SVERIFY_PROFILE=dev; select=(-m "not slow"); shift ;;
    --python) python=(--python "$2"); shift 2 ;;
    *) break ;;
  esac
done
[ ${#install[@]} -gt 0 ] || { echo "wheel_tests.sh: --wheel or --editable is required" >&2; exit 2; }

# Resolved (`/private/var` on macOS), so `--rootdir` matches the working directory.
work=$(cd "$(mktemp -d)" && pwd -P)
trap 'rm -rf "$work"' EXIT
# The repository's layout, without the repository: `python/tests`,
# `python/tools` and each engine package's `tests`. The node ids are relative
# to `python/`, as in the repository (`tests/lift_backlog.json` lists them).
mkdir -p "$work/python"
cp -r "$here/tests" "$work/python/tests"
cp -r "$here/tools" "$work/python/tools"
engine_tests=()
for e in "${engines[@]}"; do
  mkdir -p "$work/engines/$e"
  cp -r "$here/../engines/$e/tests" "$work/engines/$e/tests"
  engine_tests+=("../engines/$e/tests")
done
PYTHONPATH=$(cd "$work/python/tools" && { pwd -W 2>/dev/null || pwd; })
export PYTHONPATH
cd "$work/python"

# Each engine at the version `uv.lock` locks: the engine facts are probed at one version,
# and an install without the lock would take the newest of its range (#2592).
locked() {
  awk -v n="\"$1\"" '$0 == "name = " n { getline; gsub(/[^0-9.]/, "", $3); print $3; exit }' "$here/uv.lock"
}

# The engine release canary (#2053) tests one engine release unpinned from the lock:
# WHEEL_TESTS_ENGINE is its requirement (`duckdb==2.0.2`, `polars==2.1.1`), which replaces
# that engine's pin.
pins=()
for pkg in duckdb polars pyspark; do
  v=$(locked "$pkg")
  [ -n "$v" ] || { echo "wheel_tests.sh: no $pkg in uv.lock" >&2; exit 2; }
  case "${WHEEL_TESTS_ENGINE:-}" in "$pkg"==*) ;; *) pins+=(--with "$pkg==$v") ;; esac
done
[ -z "${WHEEL_TESTS_ENGINE:-}" ] || pins+=(--with "$WHEEL_TESTS_ENGINE")

# The test dependencies the installed package doesn't bring. Add one here
# when a test needs it, or skip the test with `pytest.importorskip`.
uv run --isolated --no-project ${python[@]+"${python[@]}"} "${install[@]}" \
  "${pins[@]}" --with pytest --with pytest-xdist --with hypothesis --with pyyaml --with mpmath \
  --with "pyiceberg[sql-sqlite]" \
  pytest -p no:cacheprovider -W "ignore:The 'future.infer_string' option is deprecated" \
  --rootdir "$work/python" \
  ${select[@]+"${select[@]}"} "$@" tests "${engine_tests[@]}"
