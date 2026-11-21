### `sverify check query.sql --schema schemas.yaml` (#1362)

A bare `.sql` file is a `check` target: one query, the types of its tables from a
YAML or JSON file (`{table: {column: type}}`), and the verdict `verify` gives with
no contract. `--dialect` and `--semantics` take `sverify.sql`'s values and defaults.
The JSON, SARIF and GitHub outputs are those of a Python file.
