### Row caps prove integer SUMs fit

A row cap `sv.max_rows(n)` in `requires` now proves integer `SUM`s fit 64
bits (#219): a `SUM` of values in `[-m, m]` over at most `n` rows, with
`n · m < 2⁶³`, is no longer an assumption checked on the data
(`Report.assumed`). Lean carries the caps through filters, unions, limits,
aggregates and joins. A join on a `unique` key of its right side keeps the
left side's rows (`Rel.capJoins_eval`), where a product would be far too
large. Caps are now:
- proved from the record counts of a Delta or Iceberg table's files;
- checked on every batch of an incremental view;
- proved in `ensures`.

`Report.rows` bounds the output's rows, and the SUM hint names the cap that
proves a sum fits.
