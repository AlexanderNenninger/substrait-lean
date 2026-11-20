### assert_contract takes the Ibis table a transform returned; SARIF results carry fixes

`sverify.testing.assert_contract` and `assert_engines_agree` take the Ibis table a contracted transform returns on Ibis tables (`assert_contract(paid(orders))`), as well as a node; `data=` gives the rows of the tables it reads, as Arrow tables, dicts or tuples ([#711](https://github.com/AlexanderNenninger/substrait-lean/issues/711)). Checking the test data and the output evaluates a table's Ibis conditions in one query.

`sverify check --format sarif`: a transform's first `needs` result carries a SARIF fix, the edits `check --fix` makes to its `requires=` ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)).
