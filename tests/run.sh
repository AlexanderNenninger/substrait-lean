#!/bin/sh
# Golden tests: run substrait-check on every fixture and compare its output
# and exit code with the recorded `.expected` file.
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
exit $fail
