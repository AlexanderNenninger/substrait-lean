# sverify

> Sverify is a working prototype. Its Lean proofs, its checker and its Python
> code still need a human audit before anyone relies on their results.
>
> [How this project is built](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-this-is-built.md)
> says who writes it and what you can check yourself.

Sverify proves a data pipeline's contracts in Lean before it runs, keeps the
result up to date from Delta and Iceberg changes, and runs the checked plan on
DuckDB, Polars and Spark.

It finds the bugs that tests on sample data miss:

* A duplicate that arrives late, or a payment that is reversed, in an incremental job ([the tour's first notebook](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/01_duplicate_payments.py)).
* Ties and NaN readings that change a window's result, and SQL that only runs alike on some engines ([second notebook](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/02_sensor_alerts.py)).
* A dbt test on a point-in-time join to a type-2 dimension, proved as a contract, and the promises a left join's NULL padding breaks ([third notebook](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/03_orders_mart.py), [what a left join keeps](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proved-theorems.md#contracts)).
* Division by zero, integer overflow and bad casts ([the runtime-error theorems](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proved-theorems.md#runtime-errors)).

[How sverify compares](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/comparison.md) with dbt tests, Great Expectations, Soda and data contracts says what it does not do.

## In thirty lines

```python
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(  # in memory; DeltaSource and IcebergSource work the same way
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)


# The upper bound on amount keeps `amount * 2` within 64 bits. Leave it out and
# the report names the bound to declare.
@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
    ensures=[_.doubled >= 22, _.doubled.notnull(), sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


big = orders.pipe(big_orders)  # proved here, before any data runs
big.refresh()  # computed, on DuckDB by default
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))
big.refresh(engine="polars", route="auto")  # updated from the changes alone, on Polars
assert big.to_arrow().to_pylist() == [{"id": 3, "doubled": 100}]
print(big_orders.report)
# proved
# The output guarantees:
#   doubled ≥ 22
#   doubled is never NULL
#   no two rows share id
# Each run checks on the data:
#   orders: amount ≥ 0
#   orders: amount < 1000000000
#   orders: no two rows share id
# ...
```

`print(big_orders.report.details())` goes on with the evidence for each engine, and `sverify check` prints the same contract.
A postcondition that does not follow is refused before anything runs, with the precondition that would make it hold
([Contracts](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-to-contracts.md)).

## Install

```bash
# skip: installs software on the reader's machine
pip install 'sverify[duckdb]'      # or: uv add 'sverify[duckdb]'; verifies and runs plans on DuckDB, the default engine
pip install sverify                # verifies only, runs nothing
pip install 'sverify[all]'         # with every engine in the 1.x promise and both table formats
```

Linux and macOS (Python 3.12 and later); Windows through WSL2.
[Install](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-to-install.md) has the extras, the wheels and the nightly builds.

## In CI

`sverify check` proves every transform and node in a pipeline file and
exits 0 when all are proved, 1 when one is not, and 3 when a construct is
outside sverify's model (the other codes are in
[the command line](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-to-command-line.md#the-command-line)). `--format sarif` writes a
report for GitHub's code scanning.

```bash
# skip: runs on pipelines/orders.py, the reader's file
sverify check pipelines/orders.py
```

## Go on from here

* [Getting started](https://alexandernenninger.github.io/substrait-lean/examples/examples.html) goes in ten steps from a first contract to Substrait's own semantics, each feature in a few lines.
* The [how-to pages](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/tasks.md) take one task each; [what sverify proves](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/what-sverify-proves.md) says what the checker proves and how the reference semantics and the engines fit.
* The [whole tour](https://github.com/AlexanderNenninger/substrait-lean/tree/main/notebooks) adds three guides, to contracts, to pipelines and engines, and to running it in production; it runs locally with `uvx marimo edit --sandbox notebooks` from a clone.
* The [API reference](https://alexandernenninger.github.io/substrait-lean/) documents every public function and class of the released version, with the [examples](https://alexandernenninger.github.io/substrait-lean/examples/examples.html) and the [ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/): the upstream bugs and Substrait spec gaps sverify found, and each engine's characterization, searchable by id, engine, function and option.
* For coding agents, the site also publishes [skills](https://alexandernenninger.github.io/substrait-lean/skills.html) for writing contracts, pipelines and engine code with sverify (`npx skills add https://alexandernenninger.github.io/substrait-lean/`); they ship in the wheel too, under `sverify/skills/`.
* [Status](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/stability.md#status) says what a prototype means for the API. To work on sverify, see the [repository](https://github.com/AlexanderNenninger/substrait-lean).

## License

Sverify is licensed under the [Mozilla Public License 2.0](https://github.com/AlexanderNenninger/substrait-lean/blob/main/LICENSE) (MPL-2.0).
You can use it in any product, open or proprietary, and your own code stays
yours. If you distribute a modified version of sverify's own files, those
files stay under the MPL and you share their source. The license applies file
by file, so it never reaches the code around them.

`python/src/sverify/ibis_substrait/` is derived from
[ibis-substrait](https://github.com/ibis-project/ibis-substrait) and stays
under the [Apache License 2.0](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/src/sverify/ibis_substrait/LICENSE).
