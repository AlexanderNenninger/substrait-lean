### Quarantine: bad rows set aside, the rest flows

A batch that breaks a precondition on a source no longer has to stop the
pipeline ([#184](https://github.com/AlexanderNenninger/substrait-lean/issues/184)).
`on_violation` on `sv.transform` or on a source chooses what a refresh does:

- `"quarantine"` sets the offending rows aside, with the reason, in a table
  next to the node's sink (`<sink>_quarantine`, or `.write(sink,
  quarantine=...)`), and the node runs on the others. A row breaks a row
  condition, or shares its key with another row: every row of a repeated
  key is set aside, so the rule needs no order and a recompute agrees with
  the batches. `Catalog.kept_sound` (`SubstraitLean/Quarantine.lean`)
  proves every precondition holds on the kept rows, so the node's proof
  holds. A delete or update upstream releases rows.
- `"skip_batch"` commits nothing for the batch and holds the node at its
  versions until a later version meets the preconditions. Conditions on a
  table as a whole (`max_rows`, `arrives_within`) hold the node this way
  under quarantine too.
- `"raise"` stays the default.

The refresh report says how many rows each refresh set aside, released and
saw deleted, with examples. `Refresh.outcome` (`"ok"`, `"quarantined"`,
`"held"`), `Refresh.alert()` (Markdown for whoever is on call) and
`Refresh.to_json()` (format 1, `sverify/schemas/refresh.schema.json`) are
new, and `Node.quarantined()` returns the rows set aside. The quarantine
table's format is stable within 1.x (`sverify/schemas/quarantine.schema.json`,
[docs/stability.md](docs/stability.md)).

`SchemaError` now names the column, the change, the version and the
contract it breaks, with what to do: "`orders.id` became nullable at v12,
and the new rows have NULLs in it; `paid` requires _.id.notnull(). Fix the
upstream, or handle NULLs in `paid` (e.g. `.fill_null(0)`) and relax
`requires`."
