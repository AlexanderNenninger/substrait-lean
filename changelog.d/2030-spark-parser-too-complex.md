### Spark names a parser refusal

When Spark's parser refuses the SQL sverify wrote for a plan as too complex (a nest of about 80 levels), the run raises `Unsupported` with the statement's size and the fact `spark-exec-parser-depth` in place of Spark's `FAILED_TO_PARSE_TOO_COMPLEX` error
([#2030](https://github.com/AlexanderNenninger/substrait-lean/issues/2030)).
