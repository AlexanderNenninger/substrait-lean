### Second and millisecond timestamps

Columns of `timestamp(0)` and `timestamp(3)` (Arrow `timestamp[s]` and `timestamp[ms]`) are now read as microseconds, exactly (D61, [#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323)). Results are `timestamp(6)`. A cast to `timestamp(0)` or `timestamp(3)` floors on the timeline, as `date_trunc` does.
