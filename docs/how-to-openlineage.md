# OpenLineage

[OpenLineage](https://openlineage.io) is the standard for lineage and run
events: Airflow, Spark and dbt emit it, and Marquez, DataHub, OpenMetadata
and the cloud catalogs read it. A refresh emits a run per node, and
`sverify.openlineage` reads what upstream jobs emitted.
The events follow spec 2-0-2, the spec of `openlineage-python` 1.55.0, and
the tests validate every event and facet against it
([tests/standards/](../python/tests/standards/openlineage-1.55.0/),
[test_openlineage.py](../python/tests/test_openlineage.py)).

```python
import tempfile

import pyarrow as pa
import sverify as sv
from ibis import _
from sverify import openlineage
from sverify.io import DeltaSink, StaticSource

lake = tempfile.mkdtemp()
shop_orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")

@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1000, sv.key("id")]},
    ensures=[_.amount > 10, _.amount < 1000, sv.key("id")],
)
def paid_orders(orders):
    return orders.filter(orders.amount > 10)

paid_sink = DeltaSink(f"{lake}/paid")
stored = shop_orders.pipe(paid_orders).write(paid_sink)
stored.refresh(lineage=openlineage.Lineage("events.jsonl", namespace="shop"))
```

The target is a file (JSON lines), `"console"`, a URL such as
`"http://marquez:5000"`, or `True` for the OpenLineage client's
configuration (`openlineage.yml`, `OPENLINEAGE_*`).

```bash
# skip: needs a Marquez service
sverify refresh pipelines/orders.py:paid --lineage http://marquez:5000
```

Sverify sends nothing and opens no connection unless a refresh gets
`lineage=` (`--lineage` on the command line). `OPENLINEAGE_DISABLED=true`
turns it off again, `OPENLINEAGE_NAMESPACE` sets the jobs' namespace and
`OPENLINEAGE_API_KEY` a bearer token (`api_key=` takes a `Secret`). A target that fails warns with
`openlineage.LineageWarning`, and the refresh goes on. The file, console
and HTTP targets need nothing; `lineage=True` reads the OpenLineage
client's configuration (any of its transports, Kafka included) and needs
`pip install 'sverify[openlineage]'`.

Each node is a job named after the node, and each refresh of it a run:
START, then COMPLETE, or FAIL with the error (a node held by a failed
precondition, or an exception), or ABORT for the nodes an earlier failure
kept from running. The run's inputs are the node's sources and the stored
nodes it reads, at their versions, with the `schema`, `dataSource` and
`version` facets, and the preconditions checked on their rows as
`dataQualityAssertions`. Its output is the node's sink, with `schema`,
`dataSource`, `version`, `outputStatistics`, the postconditions checked on
the data as `dataQualityAssertions`, and two more facets:

- `columnLineage`, from the plan Lean checked: each output column with the
  input columns it is copied (`IDENTITY`), computed (`TRANSFORMATION`) or
  aggregated (`AGGREGATION`) from, and the columns that pick the rows
  (`FILTER`, `JOIN`, `GROUP_BY`, `SORT`, `WINDOW`);
- `sverify_contract`, a custom facet with a JSON schema
  ([openlineage-contract-facet.schema.json](../python/src/sverify/schemas/openlineage-contract-facet.schema.json),
  format 1): the node, the sha256 of its plan, each postcondition with its
  status (`proved`, `checked`, `not_proved`), the preconditions, the route
  and class, the outcome, quarantined rows, and the proved plan exported
  to Substrait ([Exporting to Substrait](how-to-export.md#exporting-to-substrait);
  `Lineage(plan=False)` leaves it out).

A refresh that raises sends FAIL with the exception's type, and its text
only for sverify's own errors (`sverify.errors.SverifyError`): another
library's message may name a bucket, an endpoint or a catalog URI.
`Lineage(trace=True)` adds the Python stack trace.

Datasets are named by OpenLineage's conventions: a Delta table in object
storage is `s3://bucket` and its path, a local one `file` and its absolute
path, an Iceberg table `iceberg://<catalog>` and its identifier, and other
sources `sverify` and their name.

`openlineage.read(path)` reads events from a JSON lines file (or a list of
events), and `openlineage.marquez(url, namespace, name)` reads a dataset
from Marquez's API. `dataset(source)` gives what upstream jobs said of a
source: its `schema` as an Ibis schema, its `version`, the job that wrote
it (`producer`), and

- `requires`: the postconditions of its `sverify_contract` facet that
  sverify proves again, for a downstream transform's `requires`. The facet
  counts as proved only where it carries its exported plan and the checker
  proves that plan's postconditions (`sv.Report.from_substrait`): a contract
  chains across pipelines, repositories and teams, and each link is proved
  where it is used.
- `evidence`: everything else, as checked evidence: other
  tools' `dataQualityAssertions` (a dbt test, a Great Expectations suite),
  and the claims of a facet sverify could not prove again
  (`why_unverified` says why).

```python
# Another pipeline, in another repository, reads what `shop` wrote.
upstream = openlineage.read("events.jsonl").dataset(paid_sink)

@sv.transform(requires={"paid": upstream.requires}, ensures=[_.doubled > 20])
def doubled_paid(paid):
    return paid.select(paid.id, doubled=paid.amount * 2)

print(upstream.verified, doubled_paid.verify(paid=upstream.schema).verdict)
# True proved
```

The tests validate every emitted event and facet against OpenLineage's
published JSON schemas and check a refresh's events against Marquez: the job,
its input and output datasets, the completed run and the contract facet.
`python/scripts/marquez.sh start` runs Marquez 0.51.1 and its Postgres in
containers, with the API on port 5000, and
`SVERIFY_MARQUEZ_URL=http://localhost:5000 pytest tests/test_openlineage.py -k marquez`
runs the check; CI runs it on main and in the merge queue. DataHub takes OpenLineage events at
`/openapi/openlineage/api/v1/lineage` on its GMS, so its target is the
GMS's URL with that prefix, such as
`Lineage("http://datahub-gms:8080/openapi/openlineage", api_key=token)` with a
personal access token.
