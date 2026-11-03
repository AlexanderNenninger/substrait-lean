### Casts between doubles, decimals and integers keep their bounds

- `CAST(x AS DECIMAL(p, s))` of a double whose bounds are known no longer
  reports a failed cast or a precision overflow when the casts of the bounds
  fit: after `WHERE f BETWEEN 0 AND 100`, `CAST(f AS DECIMAL(10, 2))` is safe
  (#223).
- `CAST(d AS DOUBLE)` of a decimal keeps the decimal's bounds, as
  `CAST(n AS DOUBLE)` of an integer already does. TPC-H Q08's contract is now
  proved, and Q14's division can no longer be by zero.
- The reference computes these conversions exactly (the nearest double,
  halves to even; `round(x · 10ˢ)` in doubles for the cast to a decimal) and
  states what they keep: monotone, within `2⁻⁵³` relatively, exact for
  integers up to `2⁵³`, which survive the round trip to a double and back.
