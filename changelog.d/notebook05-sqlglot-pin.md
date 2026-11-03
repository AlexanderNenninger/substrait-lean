### Notebook 5 no longer pins SQLGlot

`05_pipelines_and_engines.py` pinned `sqlglot==30.27.0`, which conflicts with
sverify's `sqlglot~=30.17.0` from PyPI, so the notebook couldn't be published
for 0.4.0. It now takes SQLGlot from sverify.
