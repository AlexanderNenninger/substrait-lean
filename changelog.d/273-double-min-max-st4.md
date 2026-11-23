### A `MIN` or `MAX` of doubles in `to_substrait` is no longer reported as shimmed

ST-4's shim rewrites comparisons, grouping keys and sort keys of doubles, and no aggregate, yet `shims="apply"` reported a `MIN`, `MAX` or quantile of doubles as shimmed: a consumer whose `MAX` skips NaN gave another value. `"apply"` now refuses such a plan, `"annotate"` ships ST-4's assumption, and `"refuse"` refuses ([ST-4](upstream/bugs/ST-4.json), [#2505](https://github.com/AlexanderNenninger/substrait-lean/issues/2505)).
