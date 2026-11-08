#!/bin/sh
# Golden tests: run substrait-check on every fixture and compare its output
# and exit code with the recorded `.expected` file, and the same for the
# `--contract` requests and the generated lowering tables (`--lowering-coverage`).
# Pass --update to re-record the expected outputs.
set -u
cd "$(dirname "$0")/.."
bin=.lake/build/bin/substrait-check
fail=0
for plan in tests/fixtures/*.json; do
  expected="${plan%.json}.expected"
  actual=$("$bin" "$plan" 2>&1; echo "[exit $?]")
  if [ "${1:-}" = "--update" ]; then
    printf '%s\n' "$actual" > "$expected"
  elif printf '%s\n' "$actual" | diff -u "$expected" - > /dev/null; then
    echo "ok   $plan"
  else
    echo "FAIL $plan"; printf '%s\n' "$actual" | diff -u "$expected" -; fail=1
  fi
done
# The `--contract` reports (#1088): each request in tests/contracts/ (written
# by `sverify.verify`), answered through `--serve` as sverify asks.
for req in tests/contracts/*.json; do
  expected="${req%.json}.expected"
  actual=$({ printf -- '--contract %s\n' "$(wc -c < "$req" | tr -d ' ')"; cat "$req"; } |
    "$bin" --serve 2>&1; echo "[exit $?]")
  if [ "${1:-}" = "--update" ]; then
    printf '%s\n' "$actual" > "$expected"
  elif printf '%s\n' "$actual" | diff -u "$expected" - > /dev/null; then
    echo "ok   $req"
  else
    echo "FAIL $req"; printf '%s\n' "$actual" | diff -u "$expected" -; fail=1
  fi
done
# The generated lowerings (#241): which constructs are native, which guarded.
expected=tests/lowering/duckdb.expected
actual=$("$bin" --lowering-coverage 2>&1; echo "[exit $?]")
if [ "${1:-}" = "--update" ]; then
  printf '%s\n' "$actual" > "$expected"
elif printf '%s\n' "$actual" | diff -u "$expected" - > /dev/null; then
  echo "ok   $expected"
else
  echo "FAIL $expected"; printf '%s\n' "$actual" | diff -u "$expected" -; fail=1
fi
# The generated lift tables (#268): what DuckDB's SQL lifts to.
expected=tests/lowering/duckdb-lift.expected
actual=$("$bin" --lift-table 2>&1; echo "[exit $?]")
if [ "${1:-}" = "--update" ]; then
  printf '%s\n' "$actual" > "$expected"
elif printf '%s\n' "$actual" | diff -u "$expected" - > /dev/null; then
  echo "ok   $expected"
else
  echo "FAIL $expected"; printf '%s\n' "$actual" | diff -u "$expected" -; fail=1
fi
exit $fail
