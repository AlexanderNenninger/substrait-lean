### Black-box functions

DuckDB functions the checker treats as opaque now come from one table,
`SubstraitLean/BlackBox.lean` ([#325](https://github.com/AlexanderNenninger/substrait-lean/issues/325)).
Each row gives a function's types, how it treats NULL, whether it may raise,
and its laws, which the contract checker uses and Lean proves of the model.
The SQL lift reads them, the plan calls them under the URN
`extension:io.sverify:black_box`, and DuckDB runs its own function; other
engines refuse them (#271). The first two are `base64(encode(s))` (also
`to_base64`), never NULL for a string, and the aggregate `entropy(x)`, a
double at least 0, so `verify` proves `entropy(x) >= 0`. Adding a function is
adding a row ([reference semantics](docs/reference-semantics.md#black-boxes)).
