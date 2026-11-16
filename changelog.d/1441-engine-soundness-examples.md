### Spark's written plan has one model; Polars's and Spark's soundness theorems apply to an example

`Engine.polars_sound` and `Engine.spark_sound` are each applied to one example plan that meets `Engine.GuardFreeSide` ([#1441](https://github.com/AlexanderNenninger/substrait-lean/issues/1441)). Spark's written plan is modelled by `Profile.sparkWritten` alone: the hand-written `Spark.bin` is gone, and `date_add`'s wrap at 2³¹ days is a row of `Profile.spark` under `date_range` (spark-date-range). `Rel.spark_sound` keeps its name.
