#!/usr/bin/env bash
# Run QA for a pushed branch on homelab, reusing a warm Lean build.
#
# Usage, from a checkout on the laptop (the script runs on homelab and clones
# the branch there, so push it first):
#
#   ssh homelab 'bash -s -- [--wait] <branch> [poe task ...]' < python/scripts/homelab_qa.sh
#
# The script refuses to start while the box is busy (CLAUDE.md, "homelab"):
# another run's /tmp/substrait-lean-* directory with a live process in it, a
# 1-minute load above 8, or less than 6 GB available. It exits 75 and says
# why; with `--wait` it checks again every minute until the box is free (at
# most HOMELAB_QA_WAIT_MAX seconds, 3 hours by default). A directory no
# process uses is a crashed run's leftover: it gets a warning and is ignored.
# The chaos run (prefix `substrait-chaos`, below) is exempt from the run and
# load checks.
#
# The poe tasks default to `qa`. Each run clones into its own
# /tmp/<prefix>-<uuid>, which is deleted at exit, also on failure, and the
# exit status of the run is passed through.
#
# The environment can change the defaults:
#
#   PYTEST_XDIST_AUTO_NUM_WORKERS  pytest workers for `-n auto` (2: each worker
#                                  holds a Spark JVM and a Python process,
#                                  about 3 GB, so 4 pass the 8G cap)
#   HOMELAB_QA_MEMORY_MAX          memory cap of the tests (8G)
#   HOMELAB_QA_BUILD_MEMORY_MAX    memory cap of the Lean build (HOMELAB_QA_MEMORY_MAX)
#   HOMELAB_QA_NICE                niceness of the build and the tests (10)
#   HOMELAB_QA_PREFIX              the run directory's prefix (substrait-lean)
#   HOMELAB_QA_CHECK_GENERATED     check the generated modules' proofs (true)
#
# The background chaos run builds at the 8G default without checking the
# generated proofs (CI checks them on every PR), and runs its tests with 2
# workers, 2G, nice 19 and the prefix `substrait-chaos`, so the
# one-run-at-a-time check skips it (CLAUDE.md). CLAUDE.md has the capacity
# check to do before starting a run; the script refuses to start when less
# than 6 GB is available, since the build is as heavy as a QA run.
#
# The Lean build and the tests each run in their own systemd user scope with
# no swap (`ulimit -v`, per process, where user scopes are not available; a
# cap under 8G runs uncapped there, as Lean's runtime needs 8G of address
# space), so
# a runaway `lean` process is killed inside its scope before it starves the
# box. The first OOM kill stops the whole scope (`OOMPolicy=stop`): with only
# the one process killed, Lake kept the other `lean` processes thrashing at
# the cap for minutes. A failed step fails the run, and the run deletes its
# directory. To stop a run, send SIGTERM to the script's own bash (its PID):
# it stops the scope that is running and deletes the directory.
#
# The warm build is the root package's `.lake`. The `.lake` of the core,
# the analysis and engines-common are not kept: they build in about 20 s.
# `float-bounds/` and its Mathlib are not part of `poe qa`. The warm build lives
# in ~/.cache/substrait-lean/lake/<toolchain>, is copied into the clone before
# the build, and is replaced by the clone's `.lake` after a successful run.
# Lake decides what to rebuild from the hashes in its trace files, so a cache
# from another commit is safe: changed modules and their dependents rebuild.
set -uo pipefail

wait=false
if [ "${1:-}" = --wait ]; then
  wait=true
  shift
fi
branch=${1:?usage: homelab_qa.sh [--wait] <branch> [poe task ...]}
shift
tasks=("${@:-qa}")

export PATH=$HOME/.elan/bin:$HOME/.local/bin:$PATH
export PYTEST_XDIST_AUTO_NUM_WORKERS=${PYTEST_XDIST_AUTO_NUM_WORKERS:-2}
cache_root=${SUBSTRAIT_LEAN_CACHE:-$HOME/.cache/substrait-lean/lake}
keep_toolchains=2
memory_max=${HOMELAB_QA_MEMORY_MAX:-8G}
build_memory_max=${HOMELAB_QA_BUILD_MEMORY_MAX:-$memory_max}
niceness=${HOMELAB_QA_NICE:-10}
prefix=${HOMELAB_QA_PREFIX:-substrait-lean}
check_generated=${HOMELAB_QA_CHECK_GENERATED:-true}
min_available_kb=$((6 * 1024 * 1024))

max_load=8
wait_max=${HOMELAB_QA_WAIT_MAX:-10800}

waited=0

# `busy`: why the box can't take a run now, on stdout; nothing if it can.
busy() {
  local d p cwd pids born age load available_kb
  available_kb=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
  if [ "$available_kb" -lt "$min_available_kb" ]; then
    echo "only $((available_kb / 1024)) MB available, under 6 GB"
  fi
  [ "$prefix" = substrait-chaos ] && return
  load=$(cut -d' ' -f1 /proc/loadavg)
  if awk -v l="$load" -v m="$max_load" 'BEGIN { exit !(l > m) }'; then
    echo "1-minute load $load, over $max_load"
  fi
  for d in /tmp/substrait-lean-*; do
    [ -d "$d" ] || continue
    # The processes working in it: their working directory is inside it.
    pids=$(for p in /proc/[0-9]*; do
      cwd=$(readlink "$p/cwd" 2>/dev/null)
      if [ "$cwd" = "$d" ] || [[ $cwd == "$d"/* ]]; then echo "${p#/proc/}"; fi
    done | tr '\n' ' ')
    # Its age from its birth time; the modification time moves as it fills.
    born=$(stat -c %W "$d")
    [ "$born" -gt 0 ] || born=$(stat -c %Y "$d")
    age=$(( ($(date +%s) - born) / 60 ))
    if [ -n "$pids" ]; then
      echo "another run in $d, started $age min ago, PIDs $pids"
    elif [ "$waited" -eq 0 ]; then
      echo "homelab_qa: WARNING: $d ($age min old) has no process in it: a crashed run's leftover, ignored" >&2
    fi
  done
}

while reason=$(busy) && [ -n "$reason" ]; do
  if ! $wait; then
    echo "homelab_qa: not starting: $reason" | head -1 >&2
    printf '%s\n' "$reason" | tail -n +2 | sed 's/^/homelab_qa:   also: /' >&2
    exit 75
  fi
  if [ "$waited" -ge "$wait_max" ]; then
    echo "homelab_qa: still busy after $((waited / 60)) min, giving up: $reason" >&2
    exit 75
  fi
  [ $((waited % 600)) -eq 0 ] && echo "homelab_qa: waiting: $(head -1 <<< "$reason")" >&2
  sleep 60
  waited=$((waited + 60))
done

id=$(uuidgen)
dir=/tmp/$prefix-$id
unit=
trap 'rm -rf "$dir"' EXIT
trap '[ -n "$unit" ] && systemctl --user stop "$unit" 2>/dev/null; exit 143' TERM HUP INT

# Whether a user scope's MemoryMax reaches its cgroup (the memory controller
# is delegated to the user's systemd).
scopes=false
if systemd-run --user --scope --quiet -p MemoryMax=1G sh -c \
  'grep -qx 1073741824 "/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/memory.max"' \
  2>/dev/null; then
  scopes=true
fi

# `capped <step> <max> <command...>`: run the command in its own scope capped
# at <max>, at the run's niceness, and pass its exit status through.
capped() {
  local step=$1 max=$2 status
  shift 2
  if $scopes; then
    echo "homelab_qa: $step capped at $max (systemd user scope, no swap)"
    unit=$prefix-$id-$step.scope
    systemd-run --user --scope --quiet --unit="$unit" -p MemoryMax="$max" \
      -p MemorySwapMax=0 -p OOMPolicy=stop bash -c '
        nice -n "$1" "${@:2}"; status=$?
        peak=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/memory.peak
        [ -r "$peak" ] && echo "homelab_qa: peak memory, page cache included, $(numfmt --to=iec < "$peak")"
        exit $status' bash "$niceness" "$@" &
  elif [ "$(numfmt --from=iec "$max")" -lt $((8 << 30)) ]; then
    # `ulimit -v` caps address space, not memory, and Lean reserves far
    # more than it touches: under 2G `substrait-check` and under 4G `lean`
    # fail at start ("failed to create thread"), 8G runs both (#1074).
    echo "homelab_qa: WARNING: $step runs UNCAPPED: no systemd user scope, and" \
      "ulimit -v $max is too small for Lean's runtime (#1074)" >&2
    nice -n "$niceness" "$@" &
  else
    echo "homelab_qa: $step capped with ulimit -v $max (no systemd user scope)"
    (ulimit -v $(($(numfmt --from=iec "$max") / 1024)) && exec nice -n "$niceness" "$@") &
  fi
  wait $!; status=$?
  unit=
  return $status
}

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
capped build "$build_memory_max" \
  lake -R "-Kcheck_generated=$check_generated" build SubstraitLean substrait-check
status=$?
echo "homelab_qa: Lean build took $(( $(date +%s) - start )) s (exit $status)"

if [ $status -eq 0 ]; then
  capped test "$memory_max" bash -c 'cd python && exec uv run poe "$@"' bash "${tasks[@]}"
  status=$?
fi

# The cache holds builds with the generated proofs checked only.
if [ $status -eq 0 ] && [ "$check_generated" = true ]; then
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
