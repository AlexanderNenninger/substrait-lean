### Inferred preconditions for more runtime errors

Sverify now infers preconditions for runtime errors besides integer
overflow, as #244 does for overflow. Each is the weakest per-column
condition, marked "(inferred)", checked on the data or proved from metadata,
and switched off by `infer=False`:
- division and remainder by zero: `(_.b != 0)`;
- domain errors: `sqrt`, logarithms, `asin`/`acos`, a fractional power;
- casts out of range: to narrower integers, and from doubles to `BIGINT`;
- `repeat` counts;
- decimal precision of `+`, `-` and `*`;
- date arithmetic.

Where no single bound exists (`∞ / ∞`, `substring` offsets counted from
either end, the sum of two unbounded decimals), the hint suggests one and
nothing is assumed ([docs/guide.md](docs/guide.md#inferred-bounds)).
