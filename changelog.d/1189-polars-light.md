### sverify-polars installs without Polars

`sverify-polars` is the light layer of the Polars engine, as `sverify-spark`
is Spark's ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)):
its plugin and facts, enough to verify under `semantics="polars"`. Polars and
NumPy are its extra `run`, which `pip install sverify[polars]` installs as
before. A run without Polars says to install `sverify[polars]`.
