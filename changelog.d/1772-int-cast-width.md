### An integer cast gives the type it names

`t.a.cast("int32")` is an `int32` in `Report.output` and in the run, on every
engine, and so is a widening cast such as `t.b.cast("int64")` of an `int16`
column. Both were `int64` and `int16` before
([#1772](https://github.com/AlexanderNenninger/substrait-lean/issues/1772), ruling 114).
