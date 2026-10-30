# sverify

Contracts and incremental views on DataFusion, with plans that are proven
correct in Lean. See the "Incremental views in Python" section of the
[top-level README](../README.md).

```bash
(cd .. && lake build)       # builds substrait-check, which sverify calls
uv run pytest               # differential tests
uv run python scripts/capture_fixtures.py   # re-capture DataFusion fixtures
```
