### More divisors proved non-zero

`verify` now proves a divisor non-zero from more preconditions:
`(b < 0) | (b > 0)`, `(b != 0) | b.isnull()`, and a product `b * c` of
factors each known to be non-zero. Each needed a guard before.
