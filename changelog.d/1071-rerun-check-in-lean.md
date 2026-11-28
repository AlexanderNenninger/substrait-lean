### The checker decides what a rerun reproduces

The rerun check (`reproducible=` on a run, a refresh or a sink) is decided by the checker now, in one Lean function (`Realize.rerunCheck`), and Python only words its answer. The report keeps the checker's answer for the sinks' default; a stated `reproducible=` asks the checker once per plan and lenses in a process, and stated tolerances compare exactly against the plan's bound ([#1071](https://github.com/AlexanderNenninger/substrait-lean/issues/1071)).

Fixes:

- A rerun that must reproduce exact doubles (`sv.equivalent()`, `rows="sequence"`) of a double `SUM` or `AVG` with no bound on its distance to the reference passed on a test before, though two runs may differ in the last bits. It is refused now, as a postcondition is since [#2486](https://github.com/AlexanderNenninger/substrait-lean/issues/2486), naming the sinks' default (`floats="plan"`) and a tolerance with a row cap as the ways through.
- A stored report without its contract (one read back from JSON) refuses a stated `reproducible=` other than the sinks' default with "verify the plan again"; the default is still answered from the report.
