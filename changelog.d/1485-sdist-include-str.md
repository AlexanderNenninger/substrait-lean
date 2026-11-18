### The sdist carries the file the Lean statements read

The sdist now includes `tests/contracts/int_division.json`, which `SubstraitLean/Statements.lean` reads, so the wheel built from it compiles again. `tests/test_sdist_inputs.py` checks that every `include_str` path in the Lean sources is in the sdist (#1485).
