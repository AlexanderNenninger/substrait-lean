### Times in nanoseconds are refused

A table with a column of times in nanoseconds (`time64[ns]`, DuckDB's `TIME_NS`) is refused when it is added: Ibis's time type has no unit, so the plan read the column as microseconds while the engine kept the nanoseconds, and a `::TIME` cast was lost ([#627](https://github.com/AlexanderNenninger/substrait-lean/issues/627)). Cast such columns to `time64[us]` first.
