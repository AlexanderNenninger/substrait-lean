### Stable formats and a stability policy for 1.x

[docs/stability.md](docs/stability.md) states what 1.x keeps stable: the
formats a running pipeline reads, the contracts it proved, and the Python
API, which breaks in a minor release only loudly, with a test, a changelog
entry and a migration note
([#737](https://github.com/AlexanderNenninger/substrait-lean/issues/737)).

- The sink's contract record (`sverify.io.Contract`) has a `format`, 1, and
  a JSON schema, `sverify/schemas/sink-contract.schema.json`. A record
  without `format`, written before this release, reads as format 1; a
  record of a newer format is refused with an error that says to upgrade
  ([#734](https://github.com/AlexanderNenninger/substrait-lean/issues/734)).
- The Substrait contract metadata, `io.sverify.substrait.v1.Contract`,
  follows protobuf's rules for updating a message, and its manifest has a
  JSON schema, `sverify/schemas/substrait-manifest.schema.json`
  ([#735](https://github.com/AlexanderNenninger/substrait-lean/issues/735)).
- `python/tests/formats/` holds what each release wrote: Delta and Iceberg
  sinks from 0.4.0 on and Substrait exports.
  [`tests/test_formats.py`](python/tests/test_formats.py) reads them all, and
  a pipeline resumes from an old Delta sink.
