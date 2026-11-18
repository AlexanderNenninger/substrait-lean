#!/usr/bin/env bash
# Run QA for a pushed branch on homelab, reusing a warm Lean build.
#
# Usage, from a checkout on the laptop (the script runs on homelab and clones
# the branch there, so push it first):
#
#   ssh homelab 'bash -s -- [--wait] [--slots 1|2|3 | --exclusive] <branch> [poe task ...]' < python/scripts/homelab_qa.sh
#
# Slots (CLAUDE.md, "homelab"): homelab has three slots of about 4 GB, a flock
# on each, held for the life of the run. A full `poe qa` takes two
# (`--slots 2`, the default: the Lean build peaks at 4.2-4.8 GB); `--slots 1`
# suits a light task, `--slots 3` a regen and `--exclusive` a benchmark. If
# the slots aren't free the script exits 75 and says who holds them; with
# `--wait` it queues until they are (at most HOMELAB_QA_WAIT_MAX seconds, 3
# hours by default). A run that needs several slots goes before smaller runs
# that arrive after it. The kernel frees the slots when the run ends, crashes
# or is killed. Once it holds its slots, the script still checks that 6 GB are
# available (the user's own services share the box), inside the lock. Each
# holder's info is in ~/.substrait-lean/slots/slot-N.holder, and `capacity
# homelab` lists holders and waiters. The chaos run (prefix `substrait-chaos`,
# below) takes no slot.
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
#   HOMELAB_QA_WAIT_MAX            seconds `--wait` waits (10800)
#   HOMELAB_SESSION                the session's name, written to the holder info
#   HOMELAB_SLOT_DIR, HOMELAB_MIN_AVAILABLE_GB  the slot directory and memory floor (tests)
#
# The background chaos run builds at the 8G default without checking the
# generated proofs (CI checks them on every PR), and runs its tests with 2
# workers, 2G, nice 19 and the prefix `substrait-chaos`, so the
# slot check skips it (CLAUDE.md); it still needs 6 GB available.
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
slots=2
while :; do
  case ${1:-} in
    --wait) wait=true ;;
    --slots) slots=$2; shift ;;
    --exclusive) slots=all ;;
    *) break ;;
  esac
  shift
done
branch=${1:?usage: homelab_qa.sh [--wait] [--slots 1|2|3 | --exclusive] <branch> [poe task ...]}
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
wait_max=${HOMELAB_QA_WAIT_MAX:-10800}
$wait || wait_max=0

# --- slots:begin (kept identical in agentic-tools' drivers/lib/slots.sh;
# --- agentic-tools' tests/test-slots.sh compares the two copies)
# Slot pool for homelab: three slots of about 4 GB, a flock on each. Source it on homelab.
#
# A run takes an exclusive flock on its slots and keeps the descriptors for its
# whole life (children inherit them); the kernel releases them when the run
# exits, crashes or is killed. Light runs take 1 slot, a Lean build 2, a
# regen 3, a benchmark all. Runs queue at a gate lock: while one waits at the gate for its
# slots, later runs wait behind it, so a run that needs several slots is not
# starved by single-slot runs arriving after it. Slots are taken in a fixed
# order (slot-0, slot-1, slot-2). Holders and waiters write an info file so that
# `capacity homelab` can list them.
slots_dir=${HOMELAB_SLOT_DIR:-$HOME/.substrait-lean/slots}
slot_count=3
slots_min_available_kb=$(( ${HOMELAB_MIN_AVAILABLE_GB:-6} * 1024 * 1024 ))
slots_taken=()

# `slots_info <run id> <slots> <branch> <session> <command>`: the info file text.
slots_info() {
  printf 'id=%s\npid=%s\nbranch=%s\nsession=%s\nstart=%s\nslots=%s\ncmd=%s\n' \
    "$1" "$$" "$3" "$4" "$(date +%s)" "$2" "$(printf '%s' "$5" | tr '\n' ' ' | cut -c1-200)"
}

# `slots_holders`: who holds the slots now, one line each, for messages.
slots_holders() {
  local f pid
  for f in "$slots_dir"/slot-*.holder; do
    [ -f "$f" ] || continue
    pid=$(sed -n 's/^pid=//p' "$f")
    kill -0 "$pid" 2>/dev/null || continue
    echo "$(basename "$f" .holder): $(sed -n 's/^id=//p;s/^branch=//p;s/^cmd=//p' "$f" | tr '\n' ' ' | cut -c1-120)"
  done
}

# `slots_release`: remove this run's info files (the kernel frees the locks).
slots_release() {
  local i
  rm -f "$slots_dir/waiters/${slots_id:-none}"
  for i in ${slots_taken[@]+"${slots_taken[@]}"}; do rm -f "$slots_dir/slot-$i.holder"; done
}

# `slots_acquire <id> <slots> <wait seconds> <branch> <session> <command>`:
# take <slots> slots (0 wait seconds: a few seconds of grace, then exit
# status 75). Then check that 6 GB are available (HOMELAB_MIN_AVAILABLE_GB),
# inside the lock, so two runs can't both pass the check.
slots_acquire() {
  local n=$2 wait_max=$3 deadline i fd got=0 avail last=0 now
  slots_id=$1
  [ "$n" -ge 1 ] && [ "$n" -le "$slot_count" ] || { echo "slots: --slots must be 1..$slot_count" >&2; return 2; }
  mkdir -p "$slots_dir/waiters"
  slots_info "$1" "$n" "$4" "$5" "$6" > "$slots_dir/waiters/$1"
  now=$(date +%s)
  deadline=$((now + (wait_max > 0 ? wait_max : 3)))
  # The gate: one waiter at a time looks for slots, in arrival order.
  exec 19>"$slots_dir/gate"
  while ! flock -w 5 19; do
    now=$(date +%s)
    [ "$now" -lt "$deadline" ] || { echo "slots: busy: runs are queued for the slots" >&2; exec 19>&-; rm -f "$slots_dir/waiters/$1"; return 75; }
  done
  while :; do
    for ((i = 0; i < slot_count && got < n; i++)); do
      fd=$((20 + i))
      case " ${slots_taken[*]-} " in *" $i "*) continue ;; esac
      eval "exec $fd>\"$slots_dir/slot-$i\""
      if flock -n "$fd"; then slots_taken+=("$i"); got=$((got + 1)); else eval "exec $fd>&-"; fi
    done
    [ "$got" -ge "$n" ] && break
    now=$(date +%s)
    if [ "$now" -ge "$deadline" ]; then
      echo "slots: busy: need $n of $slot_count slots, held by:" >&2
      slots_holders | sed 's/^/slots:   /' >&2
      for i in "${slots_taken[@]}"; do eval "exec $((20 + i))>&-"; done
      slots_taken=(); exec 19>&-; rm -f "$slots_dir/waiters/$1"; return 75
    fi
    if [ $((now - last)) -ge 600 ]; then
      last=$now
      echo "slots: waiting for $((n - got)) more of $n slot(s); held by:" >&2
      slots_holders | sed 's/^/slots:   /' >&2
    fi
    sleep 1
  done
  for i in "${slots_taken[@]}"; do
    slots_info "$1" "$n" "$4" "$5" "$6" > "$slots_dir/slot-$i.holder.tmp" \
      && mv -f "$slots_dir/slot-$i.holder.tmp" "$slots_dir/slot-$i.holder"
  done
  rm -f "$slots_dir/waiters/$1"
  exec 19>&-
  echo "slots: holding slot(s) ${slots_taken[*]} of $slot_count" >&2
  # The memory check, with the slots held. The user's own services share the box.
  deadline=$(( $(date +%s) + (wait_max > 0 ? wait_max : 0) ))
  while :; do
    avail=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
    [ "$avail" -ge "$slots_min_available_kb" ] && return 0
    now=$(date +%s)
    if [ "$now" -ge "$deadline" ]; then
      echo "slots: not starting: only $((avail / 1024)) MB available, under $((slots_min_available_kb / 1024 / 1024)) GB" >&2
      slots_release
      return 75
    fi
    sleep 5
  done
}
# --- slots:end
[ "$slots" = all ] && slots=$slot_count

id=$(uuidgen)
if [ "$prefix" = substrait-chaos ]; then
  avail=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
  if [ "$avail" -lt "$slots_min_available_kb" ]; then
    echo "homelab_qa: not starting: only $((avail / 1024)) MB available, under 6 GB" >&2
    exit 75
  fi
else
  slots_acquire "$id" "$slots" "$wait_max" "$branch" "${HOMELAB_SESSION:-}" "poe ${tasks[*]}" || exit $?
fi
dir=/tmp/$prefix-$id
unit=
trap 'slots_release; rm -rf "$dir"' EXIT
trap 'slots_release; [ -n "$unit" ] && systemctl --user stop "$unit" 2>/dev/null; exit 143' TERM HUP INT

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
