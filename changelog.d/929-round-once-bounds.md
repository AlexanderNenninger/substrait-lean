### Double SUM and AVG bounds round once

The checker bounds a double `SUM` and `AVG` as D25 computes them, rounded
once: a mean of values in `[0, 100]` is in `[0, 100]`, with or without a row
cap, and a sum of at most `n` values in `[0, 100]` is in `[0, 100 n]`
([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
Exact postconditions such as `_.m.between(0, 100)` on an average are proved
where they needed `sv.approx` before, and casts of means need no row cap.
