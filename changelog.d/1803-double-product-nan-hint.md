### A double product's domain error names its cause

A product `x * y` of unbounded doubles is reported as a domain error (`0 * ±inf` is NaN), with the hint to bound the columns. With finite bounds the verdict is `proved_with_checks`: the overflow to `±inf` is checked on the data ([#1803](https://github.com/AlexanderNenninger/substrait-lean/issues/1803)).
