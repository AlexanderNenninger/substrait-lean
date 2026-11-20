### `--delta` names the operator that has no delta rule

`substrait-check --delta` and `NotIncrementalError` said "not incrementally maintainable (left join, fetch or window)" for every plan without a delta rule, a global aggregate and `COUNT(DISTINCT …)` included. The message now lists each blocking operator with the tables under it: `no delta rule for aggregate over orders; left join over orders, customers`.
