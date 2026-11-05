#!/usr/bin/env bash
# Run the tests as the Wheels workflow does: from a copy of python/tests and
# python/tools outside the repository, against an install with the wheel's
# runtime extras and the test dependencies listed here, nothing else. Tests
# that read repository files must carry `needs_repo` (tests/_repo.py); a
# test that imports a package missing below fails here.
#
#   wheel_tests.sh --wheel <path.whl> [--fast] [--python <version>] [pytest args...]
#   wheel_tests.sh --editable <python dir> [--fast] [--python <version>] [pytest args...]
#
# `--fast` runs `poe test`'s set: no `slow` tests, the `dev` Hypothesis
# profile. Used by `.github/workflows/wheels.yml` (the built wheel) and by
# `outside-repo` in `.github/workflows/ci.yml` (an editable install, on every
# pull request that changes python/), so the two can't drift apart.
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
install=() python=() select=()
while [ $# -gt 0 ]; do
  case "$1" in
    --wheel) install=(--with "sverify[all] @ file://$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"); shift 2 ;;
    --editable) install=(--with-editable "$(cd "$2" && pwd)[all]"); shift 2 ;;
    --fast) export SVERIFY_PROFILE=dev; select=(-m "not slow"); shift ;;
    --python) python=(--python "$2"); shift 2 ;;
    *) break ;;
  esac
done
[ ${#install[@]} -gt 0 ] || { echo "wheel_tests.sh: --wheel or --editable is required" >&2; exit 2; }

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$here/tests" "$work/tests"
cp -r "$here/tools" "$work/tools"
export PYTHONPATH="$work/tools"
cd "$work"

# The test dependencies the installed package doesn't bring. Add one here
# when a test needs it, or skip the test with `pytest.importorskip`.
uv run --isolated --no-project ${python[@]+"${python[@]}"} "${install[@]}" \
  --with pytest --with pytest-xdist --with hypothesis --with pyyaml --with mpmath \
  --with "pyiceberg[sql-sqlite]" \
  pytest -p no:cacheprovider -W "ignore:The 'future.infer_string' option is deprecated" \
  ${select[@]+"${select[@]}"} "$@" tests
