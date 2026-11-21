### Casts of booleans and dates to VARCHAR

`CAST(b AS VARCHAR)` of a boolean gives `true` or `false`, and of a date gives `YYYY-MM-DD`, in Ibis and in DuckDB SQL, with constants folded ([#346](https://github.com/AlexanderNenninger/substrait-lean/issues/346)). Polars refuses the date cast, since it has no cast from a date to a timestamp ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)). Casts of timestamps and decimals to strings stay refused until their text is decided.
