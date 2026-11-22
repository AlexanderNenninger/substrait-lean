### DuckDB 2.0.1 is probed

DuckDB 2.0.1 joins 2.0.0 as a probed version of the DuckDB table (`alsoProbed`). The sqllogictests that changed between the tags were replayed at 2.0.1: 14 cases disagree, each recorded as an engine fact ([#2045](https://github.com/AlexanderNenninger/substrait-lean/issues/2045)).
