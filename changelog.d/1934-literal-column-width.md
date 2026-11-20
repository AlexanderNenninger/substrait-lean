### A literal column has its declared width

A column projected from an integer literal now has the literal's declared type's
width, not its value's: `ibis.literal(0, "int64")` starts a 64-bit column, so
adding to it is checked at 64 bits, where sverify used to report `may fail:
overflow` at 8 bits and refuse the plan. An `int8`, `int16` or `int32` literal
keeps its narrower width ([#1934](https://github.com/AlexanderNenninger/substrait-lean/issues/1934)).
