### The reported float bounds are computed exactly

The checker evaluates the bounds behind `Report.epsilon` in exact rational
arithmetic, with square roots rounded outward and each bound written as a
decimal at least the bound
([#660](https://github.com/AlexanderNenninger/substrait-lean/issues/660)).
The `1 + 2⁻⁴⁰` factor that covered an evaluation in doubles, an unproved
step, is gone, so the bounds are slightly tighter in their last digits.
Verdicts do not change.
