### `power(-inf, y)` raises for a fractional `y`

`power(-inf, y)` for a finite `y` that is not an integer is now a domain
error of the reference, as `power(-8, 0.5)` already was. IEEE 754 gives `+inf`
(`y > 0`) or `0` (`y < 0`), as DuckDB does, but Polars's `** 0.5` gives NaN;
raising lets every engine run a verified plan without a shim. A plan that may
meet it is reported as a possible domain error, ruled out by a precondition
such as `x > float("-inf")` on the base. Integer exponents keep IEEE's value
(fact `duckdb-R15-power-neginf`). Per D17, this changes the reference and
ships in a minor version bump.
