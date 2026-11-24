### A double with no bound is not exact either

A plan whose result has a double with no bound on its distance to the reference (a `SUM` or `AVG` without `sv.max_rows`) was tested on every engine under `sv.equivalent(floats="exact")`, while a bound above zero was refused. It is refused now, naming `floats="plan"`, a row cap and `unverified=True` as the ways through. A tolerance in ulps is rounded up, and a plan with an unbounded column gets no plan tolerance ([#2486](https://github.com/AlexanderNenninger/substrait-lean/issues/2486)).
