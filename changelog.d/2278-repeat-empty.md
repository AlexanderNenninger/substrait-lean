### `repeat('', n)` returns at once

The checker returns `''` for `repeat('', n)` without counting to `n`, so a plan that repeats an empty string `2^63 - 1` times no longer hangs it ([#2278](https://github.com/AlexanderNenninger/substrait-lean/issues/2278)).
