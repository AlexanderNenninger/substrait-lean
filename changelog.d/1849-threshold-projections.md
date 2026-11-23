### Fixed: a rounded, cast or compared double that an engine computes within a bound

A projection that sends a double through `floor`, `round`, a cast to an integer,
a decimal or text, or a comparison was PROVED on an engine that computes the
double only within a bound, and could return another integer or truth value
there: `floor(x / 49.0)` was `0` on Polars, whose quotient by a constant lands
one ulp below `1`. Such plans are now refused on those engines, as a filter on
the same double is (#568's threshold rule), and run where the double is exact;
a precondition that keeps the value away from the threshold lifts the refusal
([#1849](https://github.com/AlexanderNenninger/substrait-lean/issues/1849), ruling 275).
