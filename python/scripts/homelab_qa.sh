#!/usr/bin/env bash
# Run QA for a pushed branch on homelab, reusing a warm Lean build.
#
# Usage, from a checkout on the laptop (the script runs on homelab and clones
# the branch there, so push it first):
#
#   ssh homelab 'bash -s -- <branch> [poe task ...]' < python/scripts/homelab_qa.sh
#
# The poe tasks default to `qa`. Each run clones into its own
# /tmp/substrait-lean-<uuid>, which is deleted at exit, also on failure, and
# the exit status of the run is passed through. CLAUDE.md has the capacity
# check to do before starting a run.
#
# The warm build is the root package's `.lake` (the only Lake package QA
# builds: `float-bounds/` and its Mathlib are not part of `poe qa`). It lives
# in ~/.cache/substrait-lean/lake/<toolchain>, is copied into the clone before
# the build, and is replaced by the clone's `.lake` after a successful run.
# Lake decides what to rebuild from the hashes in its trace files, so a cache
# from another commit is safe: changed modules and their dependents rebuild.
set -uo pipefail

branch=${1:?usage: homelab_qa.sh <branch> [poe task ...]}
shift
tasks=("${@:-qa}")

export PATH=$HOME/.elan/bin:$HOME/.local/bin:$PATH
export PYTEST_XDIST_AUTO_NUM_WORKERS=6
cache_root=${SUBSTRAIT_LEAN_CACHE:-$HOME/.cache/substrait-lean/lake}
keep_toolchains=2

dir=/tmp/substrait-lean-$(uuidgen)
trap 'rm -rf "$dir"' EXIT

git clone -q --branch "$branch" https://github.com/AlexanderNenninger/substrait-lean.git "$dir" \
  || exit 1
cd "$dir" || exit 1

# One cache per toolchain: `<cache_root>/<toolchain>` is a symlink to the
# snapshot it currently names, so replacing it is a single rename.
toolchain=$(tr -c 'A-Za-z0-9.\n-' '-' < lean-toolchain | head -1)
cache=$cache_root/$toolchain
mkdir -p "$cache_root"

if [ -d "$cache/" ]; then
  echo "homelab_qa: warm Lean build from $(readlink "$cache")"
  mkdir -p .lake && cp -a "$cache/." .lake/
else
  echo "homelab_qa: no warm Lean build for $toolchain, building cold"
fi

start=$(date +%s)
nice -n 10 lake -R -Kcheck_generated=true build SubstraitLean substrait-check; status=$?
echo "homelab_qa: Lean build took $(( $(date +%s) - start )) s (exit $status)"

if [ $status -eq 0 ]; then
  (cd python && nice -n 10 uv run poe "${tasks[@]}"); status=$?
fi

if [ $status -eq 0 ]; then
  # Write the new snapshot beside the old one, then swap the symlink with a
  # rename, so a failed or concurrent run never sees a half-written cache.
  # flock keeps two refreshes from racing over which old snapshot to delete.
  (
    flock -n 9 || { echo "homelab_qa: another run is refreshing the cache, skipping"; exit 0; }
    snap=$cache_root/.snap-$toolchain-$(uuidgen)
    if cp -a .lake "$snap"; then
      old=$(readlink "$cache" 2>/dev/null)
      ln -sfn "$snap" "$cache.tmp" && mv -T "$cache.tmp" "$cache"
      [ -n "$old" ] && [ "$old" != "$snap" ] && rm -rf "$old"
      echo "homelab_qa: refreshed the warm Lean build ($(du -sh "$snap" | cut -f1))"
    else
      rm -rf "$snap"
    fi
    # Bound the disk use: keep the most recently refreshed toolchains only,
    # and drop snapshots no symlink names (left by a run that was killed).
    ls -1t "$cache_root" | tail -n +$((keep_toolchains + 1)) | while read -r name; do
      rm -rf "${cache_root:?}/$name" "$(readlink -f "$cache_root/$name")"
    done
    live=$(for link in "$cache_root"/*; do readlink -f "$link"; done)
    for snapshot in "$cache_root"/.snap-*; do
      [ -d "$snapshot" ] || continue
      grep -qxF "$snapshot" <<< "$live" || rm -rf "$snapshot"
    done
  ) 9> "$cache_root/.lock"
fi

exit $status
