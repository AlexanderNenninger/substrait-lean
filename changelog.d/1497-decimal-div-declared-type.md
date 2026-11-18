### A decimal quotient's declared type must hold its value

The parser refuses a `sverify_decimal_div` whose declared `DECIMAL(p, s)` does not follow from its operands: the numerator's precision plus the upscale, or, for the `SUM` and `COUNT` of one argument, the summed argument's precision plus the upscale. Plans sverify writes are unaffected ([#1497](https://github.com/AlexanderNenninger/substrait-lean/issues/1497)).
