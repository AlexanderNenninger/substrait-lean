# sverify

Contracts and incremental views on DataFusion or Polars, with plans that are proven
correct in Lean. See the "Incremental views in Python" section of the
[top-level README](../README.md).

```bash
uv sync                     # builds substrait-check with lake and links it in
uv run pytest               # differential tests
uv run python scripts/capture_fixtures.py   # re-capture DataFusion fixtures
```
