### Polars's `round(x, d)` comes from the generated lowering

On Polars, sverify now writes `round(x, d)` from the generated lowering table,
as Polars's own `round(d, mode="half_away_from_zero")` for 0 to 22 digits.
The Lean build checks that entry, and the hand-written translation is gone.
Any other number of digits is refused before the run, as before, and the
message names the supported range (#2586).
