#!/usr/bin/env bash
# Run the tests as the Wheels workflow does: from a copy of python/tests and
# python/tools outside the repository, against an install with the wheel's
# runtime extras (`all` and the experimental `datafusion`) and the test
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

here=$(cd "$(dirname "$0")/.." && pwd)
#: The engine packages whose tests run here (`python/pyproject.toml`'s `testpaths`).
engines=(polars)
install=() python=() select=()
while [ $# -gt 0 ]; do
  case "$1" in
    --wheel) install+=(--with "sverify[all,datafusion] @ file://$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"); shift 2 ;;
    --engine-wheel) install+=(--with "$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"); shift 2 ;;
    --editable)
      install+=(--with-editable "$(cd "$2" && pwd)[all,datafusion]")
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
export PYTHONPATH="$work/python/tools"
cd "$work/python"

# The test dependencies the installed package doesn't bring. Add one here
# when a test needs it, or skip the test with `pytest.importorskip`.
uv run --isolated --no-project ${python[@]+"${python[@]}"} "${install[@]}" \
  --with pytest --with pytest-xdist --with hypothesis --with pyyaml --with mpmath \
  --with "pyiceberg[sql-sqlite]" \
  pytest -p no:cacheprovider -W "ignore:The 'future.infer_string' option is deprecated" \
  --rootdir "$work/python" \
  ${select[@]+"${select[@]}"} "$@" tests "${engine_tests[@]}"
