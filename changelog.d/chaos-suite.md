### A crash-injection suite for pipeline execution

`python/tests/chaos/` fails refreshes on purpose: an exception or a SIGKILL at
each step of a refresh (reading a source, the engine, the pipeline's state,
the cursors, a Delta or Iceberg sink before, during and after its commit),
an object store that goes away and comes back, sources that change or
vanish mid-refresh, and two processes racing on one sink. After each, the
same process or a fresh one refreshes, and every sink must equal a full
recompute of its inputs, with its epoch the sum of the versions it records.
Each failed scenario streams a record to a JSONL ledger, and
`python -m sverify_dev.chaos summarize` groups the failures by signature.
`poe test-chaos` runs it; `qa` and CI leave it out. It found
[#515](https://github.com/AlexanderNenninger/substrait-lean/issues/515),
[#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516) and
[#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517).
