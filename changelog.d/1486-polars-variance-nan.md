### Polars raises where its variance of finite values is NaN

Over finite values, Polars's ungrouped `var` can come back NaN where the reference gives a value (`[1e308] * 100000` gives NaN against the reference's 0.0). The written plan now raises `VarianceNaN`, with or without guards, and the message of the infinity raise names the algorithm's intermediate steps too ([#1486](https://github.com/AlexanderNenninger/substrait-lean/issues/1486)).
