### A verified plan for any Substrait consumer

`report.to_substrait(format="json" | "binary")` returns the verified plan for
any conforming consumer of Substrait 0.106, with each option the proof
depends on pinned in the plan, and its contract (`requires`, declared,
inferred and assumed, and `ensures`, with a manifest) as metadata in the
plan's `advanced_extensions`. `shims="apply" | "annotate" | "refuse"`
decides what happens at a spec gap: rewrite it into well-specified
Substrait, ship it as an assumption, or refuse. `sv.from_substrait` reads an
export back and proves its contract again; `report.substrait_contract()`
gives the contract as JSON for a sidecar, and `sverify.errors.ExportError`
names the gap a refusal meets
([#664](https://github.com/AlexanderNenninger/substrait-lean/issues/664),
[docs/guide.md](docs/guide.md#exporting-to-substrait)).
