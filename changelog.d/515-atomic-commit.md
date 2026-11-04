### A refresh that fails while committing changes nothing

A refresh that failed after DuckDB had updated a view's state in place (an
out-of-memory error, say) left the view ahead of its recorded source
versions, and the retry in the same process applied the batch a second
time: duplicated rows, then `changes delete rows that are not in the
inputs` or delta-rs's `rows failed validation check` in a sink. The commit
now updates the Python side first and DuckDB's state last, in one
transaction, and restores the old tables, versions and states on any
failure, so the retry applies the batch once
([#515](https://github.com/AlexanderNenninger/substrait-lean/issues/515)).
