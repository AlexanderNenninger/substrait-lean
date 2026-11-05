#!/usr/bin/env bash
# Check out sverify at the commit in SVERIFY_COMMIT under vendor/substrait-lean
# and build its checker, substrait-check, with lake (elan must be installed).
# `uv sync` then installs sverify from there (pyproject.toml's
# [tool.uv.sources]), linking the checker it built (SVERIFY_PREBUILT_CHECK).
#
# Until a sverify release has the API sverify-dbt needs (Report.needs,
# CheckedCondition.reason and .condition, DuckDB type names in
# verify(tables=...); substrait-lean#685), it is pinned to a commit. Then drop
# this script and the source, and depend on `sverify>=<that release>`.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
commit=$(cat "$root/SVERIFY_COMMIT")
repo="$root/vendor/substrait-lean"
if [ ! -d "$repo/.git" ]; then
  git clone --quiet --filter=blob:none https://github.com/AlexanderNenninger/substrait-lean "$repo"
fi
if [ "$(git -C "$repo" rev-parse HEAD)" != "$commit" ]; then
  git -C "$repo" fetch --quiet origin "$commit"
  git -C "$repo" checkout --quiet --detach "$commit"
fi
lake=$(command -v lake || echo "$HOME/.elan/bin/lake")
(cd "$repo" && "$lake" build substrait-check)
echo "SVERIFY_PREBUILT_CHECK=$repo/.lake/build/bin/substrait-check"
