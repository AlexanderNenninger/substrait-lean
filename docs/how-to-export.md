# Exporting to Substrait and ODCS

## Exporting to Substrait

`report.to_substrait(format="json" | "binary")` returns a proved plan for
any conforming Substrait consumer, with the conditions under which its proof
holds.
It is the plan the checker proved, written for Substrait 0.106:

- each call declares its YAML's URN and its compound name (`add:i64_i64`),
  and states its output type (`_substrait_extensions.json`, generated from
  the YAMLs by `python -m sverify_dev.substrait_extensions --write`);
- each option the proof depends on is pinned in the
  call's options at the reference's behaviour: `overflow`, `rounding`,
  `division_type`, `on_division_by_zero` and the rest the YAMLs list;
- a plan proved with `semantics="substrait"` goes out as it is, since its
  proof holds for every choice Substrait allows.

Where the proof uses a choice Substrait cannot state, a spec gap
([upstream ledger](https://alexandernenninger.github.io/substrait-lean/ledgers/spec-gaps.html)),
the export handles it in one of these ways:

| Gap | Handling |
|---|---|
| ST-1, ST-2, ST-5, ST-9 (overflow), ST-11, ST-12 | none needed: the reference raises there, and the preconditions, which travel with the plan, rule those inputs out (`unexercised` in the manifest) |
| ST-9 (rounding of doubles) | IEEE 754's default rounding, which `fp64` follows; recorded with evidence `tested` |
| ST-3, ST-4, ST-6 | a shim, by `shims` |
| ST-7 | none needed: the writer states every sort key's direction |
| ST-8 | none needed where no decimal `+`, `-`, `*` or cast reduces its scale and no cast takes a double to a decimal; otherwise by `shims`, with no shim |
| ST-10 | refused in every mode: `upper` and `lower` of non-ASCII text |

`shims` takes three values, applied to every gap alike:

- `"apply"` (the default) rewrites the plan into well-specified Substrait,
  so that every conforming consumer gives the reference's result. A
  `variance` or `std_dev` of too few values is NULL (ST-3). An equality of
  doubles is `x + 0.0 = y + 0.0 OR (is_nan(x) AND is_nan(y))`, a double
  grouping key is the pair `(is_nan(x), x + 0.0)`, and a double sort key
  sorts by `is_nan(x)` first, so that NaN equals NaN and sorts greatest,
  and the two zeros are one (ST-4). An ordering comparison of doubles
  (`<`, `<=`, `>`, `>=`, `between`) follows the same order. A `MIN`, `MAX`
  or quantile of doubles has no shim, so the export refuses it. A cast of a
  double to an integer truncates first (ST-6). A cast of a double to a
  decimal has no shim: Substrait leaves open both which value it rounds and
  how (ST-8, [#2523](https://github.com/AlexanderNenninger/substrait-lean/issues/2523)),
  and `"annotate"` ships the assumption that the consumer rounds the double
  product `x · 10^s` half away from zero. A gap the plan meets where no shim
  applies refuses the export.
- `"annotate"` keeps the plan as written and records each choice in the
  manifest as an assumption the consumer must honour (`assumptions`, class
  `assumed`).
- `"refuse"` refuses the export at any such gap.

A refusal raises `sverify.errors.ExportError`, which names the reason and
the gap. So does an unproved report, a plan proved under an engine's
profile, and a function outside Substrait's YAMLs.

Sverify validates the plans it exports with Substrait's own validator,
[`substrait-validator`](https://github.com/substrait-io/substrait-validator),
built at the commit the gate pins (it implements Substrait 0.88.1; no
release reads 0.106). Every coverage case and catalogue query is exported
in the `"apply"` and `"annotate"` modes, and CI's `evidence` job compares the
validator's verdicts with the ledger
[`substrait_validator.json`](../python/tests/substrait_validator.json),
[`sverify_dev.substrait_validator`](../python/tools/sverify_dev/substrait_validator.py).
On 2026-11-20: 332 exports valid, 10 with a recorded finding (time and
timestamp literals the validator does not implement yet,
[ST-19](../upstream/bugs/ST-19.json), and a decimal precision,
[#1904](https://github.com/AlexanderNenninger/substrait-lean/issues/1904)),
190 refused with their reason, 146 not proved.

`node.to_substrait()` and `transform.to_substrait()` export the report of
a node and of a transform's last call.
A node's plan is its last transform's: a contracted node upstream is a
table of that transform's name, and the contract's `requires` on it are
what that node guarantees. Export each node to cover a pipeline.

The contract travels in the plan's `advanced_extensions.optimization` as an
`io.sverify.substrait.v1.Contract` message
([`substrait_contract.proto`](../python/src/sverify/substrait_contract.proto)),
which a consumer that does not know it ignores. It holds the preconditions
(declared, inferred and assumed) and the postconditions, each in your terms
and as a Substrait plan of one boolean column, and a manifest
([`substrait-manifest.schema.json`](../python/src/sverify/schemas/substrait-manifest.schema.json)).
Within 1.x the message and the manifest only gain fields, and
`sv.Report.from_substrait` reads every earlier 1.x export
([stability.md](stability.md#the-substrait-contract-message)):

| Key | What it holds |
|---|---|
| `format`, `sverify`, `substrait` | the manifest's format version, sverify's version, `0.106.0` |
| `extension_urns` | the YAMLs the plan's calls come from |
| `semantics` | the semantics the plan was proved under |
| `class` | `exact`, `observed` (equal up to `lenses`) or `assumed` (with annotated choices) |
| `evidence` | `proved`, or `tested` where IEEE 754's default rounding stands in for an option |
| `lenses`, `lenses_components` | what the postconditions tell apart (`Report.lenses`, `sv.equivalent`) |
| `pinned` | each pinned option, its values and the calls that state it |
| `shims`, `assumptions`, `unexercised`, `up_to` | each gap and how the export handled it |
| `deterministic`, `rows`, `params`, `output` | as in the report |

`report.substrait_contract()` returns the same contract as JSON, for a
sidecar file. `sv.Report.from_substrait(exported)` reads a plan back, in either
format, and proves its contract again with the checker; the report it
returns has the same postconditions and verdict.
[Example 10](getting-started.md#10-a-proved-plan-for-any-substrait-consumer)
exports a plan and shows the three modes.

## ODCS contracts

The [Open Data Contract Standard](https://bitol-io.github.io/open-data-contract-standard/)
(ODCS, Bitol, Linux Foundation AI & Data) describes a dataset's contract in
YAML: its schema, quality rules, descriptions and owners. Sverify writes a
node's contract as ODCS and reads ODCS contracts as conditions.
It writes ODCS v3.2.0 (its `apiVersion`), and the tests validate
every export against that release's JSON schema
([tests/standards/](../python/tests/standards/odcs-json-schema-v3.2.0.json),
[test_odcs.py](../python/tests/test_odcs.py)). YAML needs PyYAML:
`pip install 'sverify[odcs]'`. JSON needs nothing.

Sverify reads the standard's own published examples, the 42 contracts of
ODCS v3.2.0's `docs/examples`
([vendored](../python/tests/standards/odcs-examples-v3.2.0/SOURCE),
[ledger](../python/tests/odcs_examples.json),
`python -m sverify_dev.odcs_examples`). It reads 151 conditions from them,
and 22 rules stay unread, each with its reason and the issue that would read
it or why it does not by design. Of the 104 schema objects with conditions,
95 export and read back to the same conditions, 4 are not tried (a foreign
key to another object) and 5 are refused on a column type sverify does not
read yet.

```python
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify import odcs
from sverify.io import StaticSource

shop_orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")

@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1000, sv.key("id")]},
    ensures=[_.amount > 10, _.amount < 1000, sv.key("id")],
)
def paid_orders(orders):
    """Paid orders over ten."""
    return orders.filter(orders.amount > 10)

odcs.write(shop_orders.pipe(paid_orders), "paid.odcs.yaml", descriptions={"id": "the order's id"})

# Another team reads the contract and builds on it.
paid_contract = odcs.read("paid.odcs.yaml")

@sv.transform(requires={"paid": paid_contract.conditions()}, ensures=[_.doubled > 20])
def doubled_paid(paid):
    return paid.select(paid.id, doubled=paid.amount * 2)

print(doubled_paid.verify(paid=paid_contract.schema()).verdict)
# proved
```

```bash
# skip: runs on pipelines/orders.py, the reader's file
sverify contract export pipelines/orders.py:paid -o paid.odcs.yaml
```

The export is one schema object named after the node, with a property per
column. Each sverify term maps to its ODCS field:

| Sverify | ODCS |
|---------|------|
| a column the node proves NOT NULL | `required: true` |
| `sv.key(...)`, the first key whose columns are all NOT NULL | `primaryKey`, `primaryKeyPosition` |
| `sv.unique(col)` | `unique: true` |
| `sv.unique(a, b)` | a `duplicateValues` rule on the object, `arguments.properties`, `mustBe: 0` |
| `_.col.isin([...])` | an `invalidValues` rule, `arguments.validValues`, `mustBe: 0` |
| `sv.max_rows(n)` | a `rowCount` rule, `mustBeLessOrEqualTo: n` |
| `sv.rows_per(cols, n)` | a `sql` rule counting the keys with more than `n` rows |
| `sv.references(col, to=...)` | a `foreignKey` relationship on the property; for several columns, on the object with `from` and `to` lists |
| any other row condition, such as a range | a `sql` rule, `SELECT COUNT(*) FROM {object} WHERE NOT COALESCE(<condition>, FALSE)`, `mustBe: 0` |
| the transform's docstring, `descriptions=` | `description` |

Every flag and rule carries a custom property `sverify` (vendor
`sverify`) with its `status`: `proved` by the checker, `checked` on the
data at every refresh (`on_unproved="check"`), or `declared` and
neither. Its `label` is the condition as the transform states it. The
document's own `sverify` property names the node, the sha256 of its plan
(as the sink's [contract record](stability.md) has it) and whether the
whole contract is proved. Sverify's conditions hold where they are TRUE, so
the SQL rules count a NULL against the condition, and a value set marks its
column `required`.

`odcs.read` takes a file, the text or a dict of ODCS 3.0 to 3.2 and gives
the conditions of each schema object (`conditions(table)`) and its columns
as an Ibis schema (`schema(table)`), for `requires` on an input or
`ensures` on a node. It reads the fields of the table above, `enum`, the
bounds in `logicalTypeOptions`, `nullValues` and `missingValues` rules,
and any `sql` rule of the form `SELECT COUNT(*) FROM {object} WHERE <rows
that break it>` that must be 0. ODCS leaves NULLs to `required`, so on a
column that may be NULL a rule on values lets NULL through. The rules it
cannot read (free text, another engine's rules, patterns, thresholds other
than 0, shares of rows, lower bounds on the row count) are listed in
`unread`, each with the reason, and `read` warns with
`odcs.UnreadRuleWarning`; `strict=True` raises instead. A round trip, ODCS
to sverify and back, keeps every rule sverify reads.
