### sverify-dbt reads dbt's files as UTF-8 on every platform

`sverify-dbt` names `encoding="utf-8"` where it reads dbt's `manifest.json`
and the selectors file it writes, so a project with non-ASCII names or
descriptions reads the same on Windows as elsewhere
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)).
