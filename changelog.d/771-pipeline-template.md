### A template repository for pipelines on GitHub

- `templates/pipelines/` holds the contents of a template repository for
  data engineering on your phone
  ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)):
  workflows that prove each pull request's pipelines and comment the
  contract in plain words (`check`), run them on staging data with a
  preview catalog (`preview`), refresh `main`'s on a schedule in a
  `production` environment (`refresh`), publish a catalog to GitHub Pages
  with DuckDB-WASM (`pages`) and open an issue when a refresh fails
  (`alerts`). Tables go to a `data` branch by default, or to your bucket
  through OIDC for enterprise. A worked pipeline keeps Eurostat's
  `nama_10_gdp` up to date, and `CLAUDE.md` with sverify's skills teaches
  Claude Code the loop. CI runs the template's steps on a recorded Eurostat
  response against every change to sverify.
