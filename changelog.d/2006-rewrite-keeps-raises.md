### A rewrite no longer runs where the plan as written may raise

`Report.run` could run a proved rewrite that dropped the part of the plan
that raises, such as a left join's unused input whose `SUM` may overflow, and
return rows where the reference raises
([#2006](https://github.com/AlexanderNenninger/substrait-lean/issues/2006)).
The rewrite now runs only where neither the plan as written nor the rewrite
has an issue; otherwise the engine runs the plan as written, and `run_gate`
says `issues`.
