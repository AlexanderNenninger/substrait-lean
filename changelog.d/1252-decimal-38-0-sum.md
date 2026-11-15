### `DECIMAL(38, 0) + DECIMAL(38, 0)` is typed

`verify` refused the sum of two `DECIMAL(38, 0)` columns because the inferred bound on them was a whole number past 64 bits, which reads as a HUGEINT. The bound is now a decimal literal, so the sum is typed as `DECIMAL(38, 0)` and its possible overflow is reported as an issue ([#1252](https://github.com/AlexanderNenninger/substrait-lean/issues/1252)).
