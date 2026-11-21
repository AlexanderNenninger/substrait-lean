### An integer cast to a timestamp in Ibis means seconds

Ibis reads `t.i.cast("timestamp")` as seconds since the epoch, as its DuckDB
backend's `to_timestamp` does; sverify read microseconds, so it proved and
ran a plan whose meaning differed from Ibis's. Sverify now reads seconds,
as `as_timestamp("s")`, and refuses `try_cast` and a time zone there
([#860](https://github.com/AlexanderNenninger/substrait-lean/issues/860)).
