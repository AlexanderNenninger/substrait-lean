### The checker names the columns a view reads

`substrait-check --reads plan.json` prints, for each table a plan reads, the columns its output needs, or `"all"` outside the incremental fragment. Sverify proves that a stored table keeping those columns, consolidated, gives the view and its delta plans (`Rel.zeval_prune`, `Rel.incremental_sound_prune`), so incremental refresh can store less of an input ([#1329](https://github.com/AlexanderNenninger/substrait-lean/issues/1329)). The checker speaks protocol 3: a sverify older than this checker refuses it with a message to upgrade.
