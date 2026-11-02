# Golden fixtures

Each `<name>.json` is a Substrait plan, and `<name>.expected` is what
`substrait-check` prints for it (`tests/run.sh`; `poe golden`, and
`tests/run.sh --update` to re-record).

The `df_*.json` plans are real plans that DataFusion's Substrait producer
wrote, with `datafusion==51.0.0`, for the Ibis pipelines in
`python/tools/sverify_dev/examples.py` (compiled to SQL by Ibis). They were
captured by `python/scripts/capture_fixtures.py`, which was deleted once
sverify stopped planning SQL with DataFusion (#211): its last version is in
the history at commit `4740130`. They are static golden inputs now. They keep
DataFusion's encodings in the golden tests, which `SubstraitLean/Parse.lean`
still reads; don't regenerate them.

The other plans are written by hand.
