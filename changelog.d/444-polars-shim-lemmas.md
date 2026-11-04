### The Polars shims, proved (#444)

Each shim and guard of the translation from the reference to Polars
(`sverify._polars_shims`) now has a Lean theorem of its name,
`Polars.<name>` in `SubstraitLean/PolarsShims.lean`: the shimmed expression
gives the reference's value, and each guard flags exactly where the
reference's precondition fails. `Polars.written_faithful` and
`Rel.polars_sound` prove the error-side rows need no shim for a verified
plan. `substrait-check --options` reports these rows as `"evidence":
"proved"` with the theorem and the facts its model rests on.
