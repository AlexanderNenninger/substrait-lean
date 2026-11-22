### Checks on data run the proved plan by default (breaking)

A check of `requires` on bound inputs, of `on_unproved="check"` on an output, of a batch at a refresh and of `Report.check_inputs` now runs each condition's plan, as the checker wrote it, on the engine of the table's `sverify.connect()` connection when no engine is named (`check_engine=None`), where it went through Ibis ([F219](docs/ledger.md#f219), [#2342](https://github.com/AlexanderNenninger/substrait-lean/issues/2342)). The count then has the reference's meaning on every engine. A condition outside the Lean model, which Ibis evaluated before, now raises `Unsupported` with the reason: write it in the subset `verify` reads. A table of another Ibis backend is still checked by Ibis there.

sverify's own DuckDB connections use the time zone UTC, so an instant (a UTC-zoned timestamp) comes back zoned UTC on a host in another zone. It used to come back in the host's zone, which the written plans refuse.
