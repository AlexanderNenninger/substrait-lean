### A decimal quotient is checked against its declared type

`sverify_decimal_div` reads as an unchecked decimal only where its declared `DECIMAL(p, s)` follows from its operands: the numerator's precision plus the upscale, or, for the `SUM` and `COUNT` of one argument, the summed argument's precision plus the upscale. Elsewhere it reads as the checked decimal, so `verify` reports an overflow where the quotient can have more digits ([#1497](https://github.com/AlexanderNenninger/substrait-lean/issues/1497)).
