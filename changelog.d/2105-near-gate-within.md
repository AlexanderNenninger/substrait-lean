### A stated float tolerance keeps the plan as written

Under `sv.equivalent(floats=sv.within(...))`, an engine now runs the plan as written in place of the checker's rewrite, as it already did under `floats="plan"`. The exception is a plan where the rewrite is proved safe at every engine's doubles: one with no double and no open measure. The report names the gate (`run_gate` is `"near"`) ([#2105](https://github.com/AlexanderNenninger/substrait-lean/issues/2105)).
