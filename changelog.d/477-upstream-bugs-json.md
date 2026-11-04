### Upstream bugs as JSON documents

The upstream bugs ledger is now one JSON document per bug,
`upstream/bugs/<id>.json`, in the format of `upstream/bug.schema.json`, and
the lift's backlog of tests is `python/tests/lift_backlog.json`, with a
reason for each test. `python -m sverify_dev.bugs` and `tests/test_bugs.py`
check both: the schema, unique ids that name their files, and that the files,
engine facts and tests they link to exist (#477).
