### Engine packages check their sverify

`sverify-duckdb`, `sverify-polars` and `sverify-spark` check at import that the installed `sverify` speaks their plugin interface, and otherwise fail with one `ImportError` that says to install both from the same release, in place of a `TypeError` from deep inside sverify (#1585). `sverify check` no longer prints a second traceback when `sverify.errors` itself fails to import; it exits 8 with the message.
