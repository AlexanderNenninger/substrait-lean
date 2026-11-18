### The first line of a report says "proved with checks"

`str(report)` and the markdown note started with `proved` for a plan proved under assumptions that a run checks on the data (`Report.assumed`), which hid what the verdict says. The line now reads `proved with checks: 2 assumptions`. The JSON `summary` carries the same text ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)).
