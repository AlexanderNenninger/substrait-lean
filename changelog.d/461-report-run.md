### A verify report runs the plan it checked

`Report.run(con, engine=None)` runs the plan a `sv.verify` report is about,
for an Ibis expression or a SQL query, with its `params` and `semantics`.
Running that plan used to take `sverify.contracts.plan_json`, outside the
public API. `Report.plan` holds the plan as Substrait JSON
([#461](https://github.com/AlexanderNenninger/substrait-lean/issues/461)).
