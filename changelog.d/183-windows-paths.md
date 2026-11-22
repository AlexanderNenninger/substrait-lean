### Windows paths in table names, file URIs and `check --fix`

Three fixes from the Windows trial
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)):

- A Delta source at a Windows path (`C:\lake\orders`) is named `orders`. It
  was named after the whole path, so a refresh, its sink record and a resume
  looked it up under another name.
- A `file:` URI keeps its drive and host: `file:///C:/db/t` and
  `file://C:\db\t` are read under `C:`, where native scans (DuckDB, Polars,
  Spark) looked under the current drive's root.
- `sverify check --fix` and `--diff` keep a file's line endings. A file with
  `\r\n` endings came back with `\r\r\n` on Windows, and `--diff` showed
  every line as changed.
