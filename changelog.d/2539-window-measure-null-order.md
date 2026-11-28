### A window's and an ordered aggregate's sort read each profile's NULL placement

Sverify's model of an engine now reads `null_order` at a window's `ORDER BY` and at an ordered
aggregate's (`string_agg`, `first`, … with `ORDER BY`), as it does at a plan's `ORDER BY`.
The option dependency report (`--dependencies`) and the transfer check list it there. Each
engine's registry entry states the relational options where its table says more than the model
reads, and `--options` prints that list as `unmodelled`: Polars's `zero_sign` at keys is on it
until its fact is probed
([#2539](https://github.com/AlexanderNenninger/substrait-lean/issues/2539)).
