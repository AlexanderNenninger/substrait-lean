### `print(report)` is the contract in plain words

`str(report)` now says what holds, what each run checks on the data and what is not proved, in the words `sverify check` uses (table names are the transform's parameters). The full text, with the semantics, the evidence for each engine, the routes and the observation, is `report.details()`, which `sverify check --full` prints (#1485).
