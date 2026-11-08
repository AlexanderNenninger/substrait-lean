### A bound on `abs(x)` bounds `x`, and a `SUM` no longer depends on `avg_int_result`

A precondition `_.x.abs() < c` or `_.x.abs() <= c` on a double now bounds
`x` between `-c` and `c`, as `_.x.between(-c, c)` does, so a window or grouped
`SUM` or `AVG` of it raises no possible domain error. A call now reads only
the options of its group that apply to it (D34): a `SUM` no longer depends on
`avg_int_result`, which kept plans such as `h2o-groupby-q1` and `ssb-q1.1`
from transferring between profiles
([#1200](https://github.com/AlexanderNenninger/substrait-lean/pull/1200)).
