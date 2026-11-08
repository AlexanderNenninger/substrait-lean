### Outputs keep credentials, data rows and stack traces to themselves

Sverify's outputs can go to CI artifacts, issues, a published catalog and a
lineage server, so three defaults changed (#887):

- Data rows are opt-in. `Refresh.to_json()` writes `"examples": []` for each
  quarantine entry unless called with `examples=True`, and
  `Refresh.alert()` gives counts, conditions and where the rows are, with
  the rows themselves only for `alert(rows=True)`. `sverify refresh` takes
  `--examples` for both. `PreconditionError.rows` and
  `QuarantineReport.examples` still hold the rows in the process.
- The OpenLineage FAIL event of a refresh that raised carries the
  exception's type, and its text only for sverify's own errors; the stack
  trace comes with `Lineage(trace=True)`. Before, every FAIL event carried
  the exception's text and the full trace.
- Every URI sverify records is written without userinfo, query string or
  fragment: a sink's `location`, `started`, `credentials[].location`, the
  ODCS `physicalName`, the OpenLineage namespace and `repr(Lineage)`. The
  user part of an Azure URI (`abfss://container@account...`), the
  container, stays. A URI that holds credentials in its userinfo counts
  as inline values, and `sverify check` warns `[inline_credentials]`.

The pipeline template's catalog publishes each table's contract record
without `cursors`, `table_ids` and `digests`, which only a resume reads.
`Source.restore` and `sink-contract.schema.json` say that a cursor is
stored in clear in the sink's table and must not be a credential.
