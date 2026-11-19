### sverify-dbt stops on a mismatched sverify, and warns on an older manifest

`import sverify_dbt` raises an `ImportError` naming the two versions when the installed `sverify` is not at sverify-dbt's version, instead of failing deep inside a check. `check` warns when `manifest.json` is not schema v12 (dbt-core 1.10 to 1.12), where it attaches tests by guesswork. The README's sample output is what `check` prints on `examples/shop` (every `accepted_values` test there is proved now), a test keeps it so, and `PROOF-STATUS.md` has the current counts, 23 of 26 (#891, 1.7 and 1.8).
