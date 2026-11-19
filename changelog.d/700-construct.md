### A refusal names its construct as data

`UnsupportedError` carries `construct` (`"function md5"` for a function,
otherwise SQL keywords in upper case such as `"WITH RECURSIVE"`) and `sql` (the
fragment the SQL lift refused; None for the Ibis producer), keyword-only and
None where a refusal sets none. The text of the error is unchanged. The Ibis
aggregates set `construct` first; the other refusals of the lift and the
producer follow
([#700](https://github.com/AlexanderNenninger/substrait-lean/issues/700)).
