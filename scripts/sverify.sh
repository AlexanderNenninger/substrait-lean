#!/usr/bin/env bash
# sverify from substrait-lean, for sverify-dbt while its API settles.
#
#   scripts/sverify.sh [REF]            check out REF and build its checker
#   scripts/sverify.sh --resolve [REF]  print the commit REF is now, only
#
# REF is a branch, a tag or a commit of substrait-lean: the first argument,
# else $SVERIFY_REF, else `main`. It is resolved to a commit on every run
# (`git ls-remote`), so `main` means the main of today. The commit is checked
# out under vendor/substrait-lean, and its checker, substrait-check, is built
# with lake (elan must be installed; lake only rebuilds what changed). The
# last line printed is SVERIFY_PREBUILT_CHECK=<path>: export it, and `uv sync`
# installs sverify from vendor/ (pyproject.toml's [tool.uv.sources]) with that
# checker linked.
set -euo pipefail
url=https://github.com/AlexanderNenninger/substrait-lean
root=$(cd "$(dirname "$0")/.." && pwd)
repo="$root/vendor/substrait-lean"

resolve_only=false
if [ "${1:-}" = --resolve ]; then
  resolve_only=true
  shift
fi
ref=${1:-${SVERIFY_REF:-main}}

if [[ $ref =~ ^[0-9a-f]{40}$ ]]; then
  commit=$ref
else
  commit=$(git ls-remote "$url" "refs/heads/$ref" "refs/tags/$ref^{}" "refs/tags/$ref" \
    | head -1 | cut -f1)
  if [ -z "$commit" ]; then
    echo "sverify.sh: substrait-lean has no branch or tag $ref" >&2
    exit 1
  fi
fi
if $resolve_only; then
  echo "$commit"
  exit 0
fi
echo "sverify: substrait-lean $ref at $commit" >&2

# vendor/substrait-lean may hold a cached .lake without a checkout.
if [ ! -d "$repo/.git" ]; then
  mkdir -p "$repo"
  git -C "$repo" init --quiet
  git -C "$repo" remote add origin "$url"
fi
if [ "$(git -C "$repo" rev-parse --verify --quiet HEAD || true)" != "$commit" ]; then
  git -C "$repo" fetch --quiet --depth 1 origin "$commit"
  git -C "$repo" checkout --quiet --force --detach "$commit"
fi
lake=$(command -v lake || echo "$HOME/.elan/bin/lake")
(cd "$repo" && "$lake" build substrait-check >&2)
echo "SVERIFY_PREBUILT_CHECK=$repo/.lake/build/bin/substrait-check"
