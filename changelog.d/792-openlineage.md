### OpenLineage

A refresh emits OpenLineage run events with `lineage=` (`sverify refresh
--lineage` on the command line), to a JSON lines file, the console, an
HTTP endpoint such as Marquez or DataHub, or any transport the OpenLineage
client's configuration names
([#792](https://github.com/AlexanderNenninger/substrait-lean/issues/792)).
Each node is a job and each refresh a run, with its inputs and outputs at
their versions, `schema`, `columnLineage` from the plan,
`dataQualityAssertions` for the conditions checked on data, and a
versioned `sverify_contract` facet with the contract, each
postcondition's status, the route, quarantined rows and the verified plan.
`sverify.openlineage.read` and `marquez` read upstream events: a
`sverify_contract` facet that sverify proves again becomes a downstream
transform's `requires`, and other tools' assertions are checked evidence.
Off by default. The new extra `sverify[openlineage]` installs the
OpenLineage client for its configuration.
