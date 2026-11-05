### The report as JSON

`Report.to_json()` writes a report as a versioned JSON document for CI jobs
and tools, and `Report.from_json()` reads it back into a `Report` with the
same verdict
([#736](https://github.com/AlexanderNenninger/substrait-lean/issues/736)).
The document holds the verdict, each postcondition with its reason, message
and counterexample, the runtime issues and assumptions, what the proof needs
(`Report.needs`), the facts, the non-NULL columns and the routes. Its format
is 1, with a JSON schema, `sverify/schemas/report.schema.json`, and follows
the rules of [docs/stability.md](docs/stability.md): within 1.x it only gains
keys, and a reader refuses a newer format with an error that says to
upgrade. `python/tests/formats/` holds reports for
[`tests/test_formats.py`](python/tests/test_formats.py) to read back.
