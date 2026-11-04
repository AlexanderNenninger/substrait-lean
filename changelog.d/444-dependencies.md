### The options a plan meets, and whether its proof transfers

`substrait-check --dependencies <plan.json>` lists the options a plan meets,
with the reference's, DuckDB's and Polars's choice at each. It says, for each
pair of profiles, whether a proof under the first holds under the second, and
which shims each engine needs for the plan. Lean proves the check sound
(`Rel.transfer_of_transferB`,
[#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
