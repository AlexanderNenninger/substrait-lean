### A report read back keeps its run-time checks

`Report.to_json` now writes what a run checks on the data (the margin checks of threshold filters on double sums, the pair counts of as-of joins and the as-of join's cap) and `Report.from_json` reads it back; a plan read by `Report.from_substrait` keeps the cap ([#1863](https://github.com/AlexanderNenninger/substrait-lean/issues/1863)).
