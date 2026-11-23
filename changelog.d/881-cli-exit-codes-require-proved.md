### Breaking: two more exit codes; `check --require-proved`; relaxations in the JSON (#881 S1, S2, 1.3)

- `sverify` exits 3 only for a construct outside the model. A proved node with
  no route to the engine (`refresh`) exits 4, `status` `"refused"`. A refresh
  that held a node exits 7, `status` `"held"`; 6 is for rows quarantined.
  `cli.schema.json` allows `exit` up to 8, and the codes run from the best to the
  worst (#2458).
- `sverify check --require-proved` exits 1 for a node whose unproved
  postconditions are only checked on the data (`on_unproved="check"`), with a
  `checked_only` finding that `sverify explain` describes. The pipeline
  template's check workflow passes it.
- Each item of the JSON has `relaxations`, the settings of its transform that
  weaken the gate (`on_unproved="check"`, `on_inferred="ignore"`, `"off"` or
  `"warn"`, `check_requires=False`), for a CI step to diff between base and head.
- A report's text for an assumed-finite operation says the plan raises and
  commits nothing on overflow, where it said the data is refused before the run.
- `docs/stability.md` says what the promise covers of the checker binary.
