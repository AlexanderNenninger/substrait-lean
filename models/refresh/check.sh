#!/usr/bin/env bash
# Check the refresh protocol's TLA+ model with TLC (models/refresh/README.md).
#
#   bash models/refresh/check.sh                    # every config but deep-*
#   bash models/refresh/check.sh fixed-one-writer   # some of them
#   DEEP=1 bash models/refresh/check.sh            # with the deep-* configs
#
# Each config's first line says what TLC must find: `pass`, or
# `violated <Invariant or Property>`. The script fails when a run finds
# anything else, and prints the states, the time and the outcome of each.
#
# Environment: TLA2TOOLS (default ~/.local/share/tlaplus/tla2tools.jar),
# TLC_WORKERS (2), TLC_HEAP (2g, per config), TLC_JOBS (1: configs run one
# after another; more run them side by side), TLC_OUT (a directory to keep TLC's output
# and traces in; default a temporary one, deleted).
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
jar=${TLA2TOOLS:-$HOME/.local/share/tlaplus/tla2tools.jar}
workers=${TLC_WORKERS:-2}
heap=${TLC_HEAP:-2g}
if [ ! -f "$jar" ]; then
    echo "no tla2tools.jar at $jar: set TLA2TOOLS (README.md says where to get it)" >&2
    exit 2
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
out=${TLC_OUT:-$tmp/out}
mkdir -p "$out"

if [ $# -eq 0 ]; then
    # The deep configs take tens of minutes: only with DEEP=1, or by name.
    set -- $(cd "$here/configs" && ls *.cfg | sed 's/\.cfg$//' | { if [ -n "${DEEP:-}" ]; then cat; else grep -v '^deep-'; fi; })
fi

jobs=${TLC_JOBS:-1}

run() {
    # One config: its row of the table in "$out/$1.row", its log in "$out/$1.out".
    name=$1
    cfg="$here/configs/$name.cfg"
    expect=$(sed -n '1s/^\\\* expect: //p' "$cfg")
    start=$(date +%s)
    (cd "$here" && java -XX:+UseParallelGC -Xmx"$heap" -cp "$jar" tlc2.TLC \
        -workers "$workers" -metadir "$tmp/meta-$name" -config "$cfg" Refresh.tla) \
        > "$out/$name.out" 2>&1 || true
    secs=$(( $(date +%s) - start ))
    log="$out/$name.out"
    if grep -q 'Model checking completed. No error has been found.' "$log"; then
        found=pass
    elif inv=$(sed -n 's/^Error: Invariant \([A-Za-z0-9_]*\) is violated.*/\1/p' "$log" | head -1) && [ -n "$inv" ]; then
        found="violated $inv"
    elif grep -q 'Temporal properties were violated' "$log"; then
        found="violated $(sed -n 's/^PROPERTIES //p' "$cfg")"
    elif grep -q 'Deadlock reached' "$log"; then
        found=deadlock
    else
        found=error
    fi
    distinct=$(sed -n 's/.* \([0-9][0-9]*\) distinct states found.*/\1/p' "$log" | tail -1)
    printf '%s\t%s\t%s\t%s\n' "$expect" "$found" "${distinct:-?}" "$secs" > "$out/$name.row"
}

# With TLC_JOBS above 1, configs run side by side, the largest first: most
# of them take a second or two, spent starting the JVM.
start_all=$(date +%s)
for name in $(printf '%s\n' "$@" | awk '{print (/^(deep-|fixed-two)/ ? 0 : 1) "\t" $0}' | sort -s -k1,1n | cut -f2); do
    if [ "$jobs" -le 1 ]; then
        run "$name"
    else
        while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do sleep 0.2; done
        run "$name" &
    fi
done
wait

failed=0
printf '%-26s %-30s %-30s %12s %8s\n' config expected found distinct seconds
for name in "$@"; do
    IFS=$(printf '\t') read -r expect found distinct secs < "$out/$name.row"
    printf '%-26s %-30s %-30s %12s %8s\n' "$name" "$expect" "$found" "$distinct" "$secs"
    if [ "$found" != "$expect" ]; then
        failed=1
        echo "  unexpected: see $out/$name.out" >&2
        [ -z "${TLC_OUT:-}" ] && tail -30 "$out/$name.out" >&2
    fi
done
echo "all configs: $(( $(date +%s) - start_all )) s"
exit $failed
